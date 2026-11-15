-- Prove2me | Definitions.Def_RPLib_S3_DWSTateB
-- name    : RPLib_S3_DWSTateB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:18:00.817184+00:00
-- url     : https://prove2.me/theorems/82d7cf89-7b78-45c6-92db-c8b46fd7628b
-- title:
--   Weight-two Ramanujan-Petersson library: `End_{F_q}(E)` of an ordinary curve as an abstract quadratic order
-- statement:
--   `End_{F_q}(E)` of an ordinary curve as an abstract quadratic order.
--
--   * `OrdData W L`: the conclusion of `endFq_ordinary` packaged as a structure (`f`, `b`, `w` with
--     `End_{F_q}(E) = ℤ + ℤ w`, `f w = π - b`, `w² - tr(w) w + deg(w) = 0`); `exists_ordData`.
--   * `Ord d := QuadraticAlgebra ℤ (-deg w) (tr w)` (`ω² = -deg w + tr(w) ω`), a domain (`Ord.isDomain`).
--   * `θ d : Ord d →ₐ[ℤ] AddMonoid.End E(L)`, `ω ↦ w`: `θ_apply`, `θ_injective`, `θ_mem`, `exists_θ_eq`
--     (`range = End_{F_q}(E)`), `θ_pi` (`θ ⟨b, f⟩ = π`), `θ_mul_comm`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateA
import Definitions.Def_RPLib_S3_DWSTateQ1

/-!
# S3-DWS-Tate, part B: `End_{F_q}(E)` of an ordinary curve as an abstract quadratic order

* `OrdData W L`: the conclusion of `endFq_ordinary` packaged as a structure (`f`, `b`, `w` with
  `End_{F_q}(E) = ℤ + ℤ w`, `f w = π - b`, `w² - tr(w) w + deg(w) = 0`); `exists_ordData`.
* `Ord d := QuadraticAlgebra ℤ (-deg w) (tr w)` (`ω² = -deg w + tr(w) ω`), a domain (`Ord.isDomain`).
* `θ d : Ord d →ₐ[ℤ] AddMonoid.End E(L)`, `ω ↦ w`: `θ_apply`, `θ_injective`, `θ_mem`, `exists_θ_eq`
  (`range = End_{F_q}(E)`), `θ_pi` (`θ ⟨b, f⟩ = π`), `θ_mul_comm`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Ord

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

variable (W L) in
/-- `End_{F_q}(E) = ℤ + ℤ w` for an ordinary curve (the conclusion of `endFq_ordinary`). -/
structure OrdData where
  f : ℤ
  b : ℤ
  w : AddMonoid.End (Pt W L)
  f_pos : 0 < f
  mem : w ∈ endFq W L
  hfw : (f : AddMonoid.End (Pt W L)) * w = piE W L - (b : AddMonoid.End (Pt W L))
  basis : ∀ φ ∈ endFq W L, ∃ i j : ℤ,
    φ = (i : AddMonoid.End (Pt W L)) + (j : AddMonoid.End (Pt W L)) * w
  indep : ∀ i j : ℤ, (i : AddMonoid.End (Pt W L)) + (j : AddMonoid.End (Pt W L)) * w = 0 → i = 0 ∧ j = 0
  rel : w * w - (tr w : AddMonoid.End (Pt W L)) * w + ((deg w : ℤ) : AddMonoid.End (Pt W L)) = 0
  neg : tr w ^ 2 < 4 * (deg w : ℤ)
  htr : RPLib.EllFq.trace W = 2 * b + f * tr w
  hq : (Fintype.card F : ℤ) = b ^ 2 + f * tr w * b + f ^ 2 * (deg w : ℤ)
  comm : ∀ φ ∈ endFq W L, ∀ ψ ∈ endFq W L, φ * ψ = ψ * φ

theorem exists_ordData (h : ¬ ((ringChar F : ℤ) ∣ RPLib.EllFq.trace W)) : Nonempty (OrdData W L) := by
  obtain ⟨-, hc, f, b, w, hf, hw, hfw, hbasis, hindep, -, hrel, hneg, htr, hq, -⟩ := endFq_ordinary (L := L) h
  exact ⟨⟨f, b, w, hf, hw, hfw, hbasis, hindep, hrel, hneg, htr, hq, hc⟩⟩

/-- The abstract order `ℤ[ω]`, `ω² = -deg(w) + tr(w) ω`. -/
abbrev Ord (d : OrdData W L) : Type := QuadraticAlgebra ℤ (-(deg d.w : ℤ)) (tr d.w)

theorem OrdData.disc_neg (d : OrdData W L) : tr d.w ^ 2 + 4 * (-(deg d.w : ℤ)) < 0 := by
  have := d.neg; linarith

instance Ord.isDomain (d : OrdData W L) : IsDomain (Ord d) := QA.isDomain d.disc_neg

theorem OrdData.sq (d : OrdData W L) :
    d.w * d.w = (-(deg d.w : ℤ)) • (1 : AddMonoid.End (Pt W L)) + tr d.w • d.w := by
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_one, Int.cast_neg]
  have h := d.rel
  rw [← sub_eq_zero, ← h]
  abel

/-- `θ : ℤ[ω] → End(E(L))`, `ω ↦ w`. -/
noncomputable def θ (d : OrdData W L) : Ord d →ₐ[ℤ] AddMonoid.End (Pt W L) :=
  QuadraticAlgebra.lift ⟨d.w, d.sq⟩

theorem θ_apply (d : OrdData W L) (z : Ord d) :
    θ d z = (z.re : AddMonoid.End (Pt W L)) + (z.im : AddMonoid.End (Pt W L)) * d.w := by
  simp only [θ, QuadraticAlgebra.lift_apply_apply, zsmul_eq_mul, mul_one]

theorem θ_mk (d : OrdData W L) (x y : ℤ) :
    θ d (⟨x, y⟩ : Ord d) = (x : AddMonoid.End (Pt W L)) + (y : AddMonoid.End (Pt W L)) * d.w :=
  θ_apply d _

theorem θ_injective (d : OrdData W L) : Function.Injective (θ d) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  rw [θ_apply] at hz
  obtain ⟨h1, h2⟩ := d.indep _ _ hz
  ext
  · exact h1
  · exact h2

theorem θ_mem (d : OrdData W L) (z : Ord d) : θ d z ∈ endFq W L := by
  rw [θ_apply]
  exact (endFq W L).add_mem (intCast_mem (endFq W L) _)
    ((endFq W L).mul_mem (intCast_mem (endFq W L) _) d.mem)

theorem exists_θ_eq (d : OrdData W L) {φ : AddMonoid.End (Pt W L)} (hφ : φ ∈ endFq W L) :
    ∃ z : Ord d, θ d z = φ := by
  obtain ⟨i, j, rfl⟩ := d.basis φ hφ
  exact ⟨⟨i, j⟩, θ_mk d i j⟩

theorem mem_endFq_iff_θ (d : OrdData W L) {φ : AddMonoid.End (Pt W L)} :
    φ ∈ endFq W L ↔ ∃ z : Ord d, θ d z = φ :=
  ⟨exists_θ_eq d, fun ⟨z, hz⟩ => hz ▸ θ_mem d z⟩

theorem θ_pi (d : OrdData W L) : θ d (⟨d.b, d.f⟩ : Ord d) = piE W L := by
  rw [θ_mk, d.hfw]
  abel

theorem θ_intCast (d : OrdData W L) (n : ℤ) : θ d (n : Ord d) = (n : AddMonoid.End (Pt W L)) := map_intCast _ n

theorem θ_mul_comm (d : OrdData W L) (z : Ord d) (φ : AddMonoid.End (Pt W L)) (hφ : φ ∈ endFq W L) :
    θ d z * φ = φ * θ d z :=
  d.comm _ (θ_mem d z) _ hφ

theorem θ_eq_θ_iff (d : OrdData W L) {z z' : Ord d} : θ d z = θ d z' ↔ z = z' :=
  (θ_injective d).eq_iff

end Ord

end RPLib.DWS


