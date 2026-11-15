-- Prove2me | Definitions.Def_RPLib_S3_DWSTateA
-- name    : RPLib_S3_DWSTateA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:09:54.015373+00:00
-- url     : https://prove2.me/theorems/264e68ca-e91e-4c9f-a569-5098006fd9b1
-- title:
--   Weight-two Ramanujan-Petersson library: Tate's theorem in library form, and kernels `E[S]` of sets of endomorphisms
-- statement:
--   Tate's theorem in library form, and kernels `E[S]` of sets of endomorphisms.
--
--   * `TateIsogLib F L` : Tate's isogeny theorem in the language of `DWSIsog` (`IsIsogenous`). The pure-Mathlib
--     hypothesis is `TateIsogenyStatement` (file `TateStmt`); the bridge between the two is a separate obligation.
--   * `numPoints_eq_iff_trace_eq`, `trace_eq_of_isIsogenous`.
--   * `kerSet S` (`E[S]`, the common kernel of a set `S` of additive endomorphisms of `E(L)`), `mem_kerSet`,
--     `kerSet_anti`, `kerSet_union`, `kerSet_le_tors`, `kerSet_mul_right` (`E[Sα] = α⁻¹ E[S]`), `frob_mem_kerSet`,
--     `finite_kerSet`, `card_kerSet_ne_zero` (`p ∤ #E[S]` when `S` contains an integer `N` with `p ∤ N`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsog
import Definitions.Def_RPLib_S3_TateStmt

/-!
# S3-DWS-Tate, part A: Tate's theorem in library form, and kernels `E[S]` of sets of endomorphisms

* `TateIsogLib F L` : Tate's isogeny theorem in the language of `DWSIsog` (`IsIsogenous`). The pure-Mathlib
  hypothesis is `TateIsogenyStatement` (file `TateStmt`); the bridge between the two is a separate obligation.
* `numPoints_eq_iff_trace_eq`, `trace_eq_of_isIsogenous`.
* `kerSet S` (`E[S]`, the common kernel of a set `S` of additive endomorphisms of `E(L)`), `mem_kerSet`,
  `kerSet_anti`, `kerSet_union`, `kerSet_le_tors`, `kerSet_mul_right` (`E[Sα] = α⁻¹ E[S]`), `frob_mem_kerSet`,
  `finite_kerSet`, `card_kerSet_ne_zero` (`p ∤ #E[S]` when `S` contains an integer `N` with `p ∤ N`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Lib

variable (F : Type*) [Field F] [Fintype F] (L : Type*) [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

/-- **Tate's isogeny theorem in library form**: elliptic curves over `F` with the same trace are `F`-isogenous. -/
def TateIsogLib : Prop :=
  ∀ (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic],
    RPLib.EllFq.trace W = RPLib.EllFq.trace W' → IsIsogenous W W' L

variable {F}

theorem numPoints_eq_iff_trace_eq (W W' : WeierstrassCurve F) :
    RPLib.EllFq.numPoints W = RPLib.EllFq.numPoints W' ↔ RPLib.EllFq.trace W = RPLib.EllFq.trace W' := by
  unfold RPLib.EllFq.trace
  constructor
  · intro h; rw [h]
  · intro h
    have : (RPLib.EllFq.numPoints W : ℤ) = RPLib.EllFq.numPoints W' := by linarith
    exact_mod_cast this

end Lib

section Ker

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

/-- `E[S]`: the common kernel of a set `S` of additive endomorphisms of `E(L)`. -/
def kerSet (S : Set (AddMonoid.End (Pt W L))) : AddSubgroup (Pt W L) where
  carrier := {P | ∀ α ∈ S, α P = 0}
  add_mem' := by
    intro P Q hP hQ α hα
    rw [map_add, hP α hα, hQ α hα, add_zero]
  zero_mem' := fun α _ => map_zero α
  neg_mem' := by
    intro P hP α hα
    rw [map_neg, hP α hα, neg_zero]

lemma mem_kerSet {S : Set (AddMonoid.End (Pt W L))} {P : Pt W L} :
    P ∈ kerSet S ↔ ∀ α ∈ S, α P = 0 := Iff.rfl

lemma kerSet_anti {S T : Set (AddMonoid.End (Pt W L))} (h : S ⊆ T) : kerSet T ≤ kerSet S :=
  fun _ hP α hα => hP α (h hα)

lemma kerSet_union (S T : Set (AddMonoid.End (Pt W L))) : kerSet (S ∪ T) = kerSet S ⊓ kerSet T := by
  ext P
  simp only [AddSubgroup.mem_inf, mem_kerSet, Set.mem_union]
  constructor
  · intro h; exact ⟨fun α hα => h α (Or.inl hα), fun α hα => h α (Or.inr hα)⟩
  · rintro ⟨h₁, h₂⟩ α (hα | hα)
    · exact h₁ α hα
    · exact h₂ α hα

/-- `E[S] ⊆ E[N]` when the integer `N` lies in `S`. -/
lemma kerSet_le_tors {S : Set (AddMonoid.End (Pt W L))} {N : ℕ} (hN : (N : AddMonoid.End (Pt W L)) ∈ S) :
    kerSet S ≤ RPLib.Torsion.tors (W.baseChange L) N := by
  intro P hP
  have := hP _ hN
  rw [AddMonoid.End.natCast_apply] at this
  exact RPLib.Torsion.mem_tors.mpr this

/-- `E[S α] = α⁻¹ E[S]`. -/
lemma kerSet_mul_right (S : Set (AddMonoid.End (Pt W L))) (α : AddMonoid.End (Pt W L)) :
    kerSet ((· * α) '' S) = (kerSet S).comap α := by
  ext P
  simp only [mem_kerSet, Set.mem_image]
  constructor
  · intro h x hx
    exact h (x * α) ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact h x hx

/-- `E[S]` is Frobenius-stable when every element of `S` commutes with Frobenius. -/
lemma frob_mem_kerSet {S : Set (AddMonoid.End (Pt W L))}
    (hS : ∀ α ∈ S, piE W L * α = α * piE W L) {P : Pt W L} (hP : P ∈ kerSet S) :
    RPLib.EllFq.frob W L P ∈ kerSet S := by
  intro α hα
  have h := congrArg (fun χ : AddMonoid.End (Pt W L) => χ P) (hS α hα)
  change piE W L (α P) = α (piE W L P) at h
  rw [hP α hα, map_zero] at h
  exact h.symm

lemma frob_mem_kerSet_of_le {S : Set (AddMonoid.End (Pt W L))} (hS : S ⊆ endFq W L) {P : Pt W L}
    (hP : P ∈ kerSet S) : RPLib.EllFq.frob W L P ∈ kerSet S :=
  frob_mem_kerSet (fun _ hα => (mem_endFq.mp (hS hα)).2) hP

/-- `E[S]` is finite when `S` contains an integer `N` prime to `p`. -/
lemma finite_kerSet {S : Set (AddMonoid.End (Pt W L))} {N : ℕ}
    (hN : (N : AddMonoid.End (Pt W L)) ∈ S) (hNF : (N : F) ≠ 0) : Finite (kerSet S) := by
  have hc := RPLib.Torsion.card_tors_baseChange (W := W) L N hNF
  have hpos : Nat.card (RPLib.Torsion.tors (W.baseChange L) N) ≠ 0 := by
    rw [hc]
    exact pow_ne_zero 2 (fun h => hNF (by rw [h, Nat.cast_zero]))
  have : Finite (RPLib.Torsion.tors (W.baseChange L) N) := Nat.finite_of_card_ne_zero hpos
  exact Finite.of_injective _ (AddSubgroup.inclusion_injective (kerSet_le_tors hN))

/-- `p ∤ #E[S]` when `S` contains an integer `N` prime to `p`. -/
lemma card_kerSet_ne_zero {S : Set (AddMonoid.End (Pt W L))} {N : ℕ}
    (hN : (N : AddMonoid.End (Pt W L)) ∈ S) (hNF : (N : F) ≠ 0) :
    (Nat.card (kerSet S) : L) ≠ 0 := by
  have hc := RPLib.Torsion.card_tors_baseChange (W := W) L N hNF
  have hdvd : Nat.card (kerSet S) ∣ N ^ 2 := by
    rw [← hc]
    exact AddSubgroup.card_dvd_of_le (kerSet_le_tors hN)
  obtain ⟨k, hk⟩ := hdvd
  intro h0
  have hNL : (N : L) ≠ 0 := by
    rw [← map_natCast (algebraMap F L)]
    exact (map_ne_zero_iff _ (algebraMap F L).injective).mpr hNF
  apply pow_ne_zero 2 hNL
  have : ((N ^ 2 : ℕ) : L) = 0 := by rw [hk, Nat.cast_mul, h0, zero_mul]
  exact_mod_cast this

end Ker

end RPLib.DWS


