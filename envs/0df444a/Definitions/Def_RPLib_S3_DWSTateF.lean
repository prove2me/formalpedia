-- Prove2me | Definitions.Def_RPLib_S3_DWSTateF
-- name    : RPLib_S3_DWSTateF
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:28:13.841204+00:00
-- url     : https://prove2.me/theorems/c6e87ad8-54ce-409f-ae05-3a9a075b92d2
-- title:
--   Weight-two Ramanujan-Petersson library: kernel ideals (b3) and `End_{F_q}(E/E[I]) = ι_I(O)` (b4)
-- statement:
--   Kernel ideals (b3) and `End_{F_q}(E/E[I]) = ι_I(O)` (b4).
--
--   Hypothesis on the ideal: `I * J = (N)` for some ideal `J` and an integer `N` prime to `p` (every invertible ideal of
--   norm prime to `p`, with `J = Ī`, `N = N(I)`).
--   Everything is stated for an `R`-structure `s : OAct R W L` (e.g. `OrdData.toOAct d`).
--   * `ι_mem_kerI_of_tors` : `ι(β) E[N] ⊆ E[I]` for `β ∈ J`.
--   * `mem_of_kills_kerI` (b3) : `α` kills `E[I]` ⇒ `α ∈ I`, i.e. `Ann(E[I]) = I`.
--   * `exists_mul_γ`, `exists_ιq_eq` (b4) : every `γ ∈ End_{F_q}(E/E[I])` is `ι_I(α)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateE

/-!
# S3-DWS-Tate, part F: kernel ideals (b3) and `End_{F_q}(E/E[I]) = ι_I(O)` (b4)

Hypothesis on the ideal: `I * J = (N)` for some ideal `J` and an integer `N` prime to `p` (every invertible ideal of
norm prime to `p`, with `J = Ī`, `N = N(I)`).
Everything is stated for an `R`-structure `s : OAct R W L` (e.g. `OrdData.toOAct d`).
* `ι_mem_kerI_of_tors` : `ι(β) E[N] ⊆ E[I]` for `β ∈ J`.
* `mem_of_kills_kerI` (b3) : `α` kills `E[I]` ⇒ `α ∈ I`, i.e. `Ann(E[I]) = I`.
* `exists_mul_γ`, `exists_ιq_eq` (b4) : every `γ ∈ End_{F_q}(E/E[I])` is `ι_I(α)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section KI

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {R : Type*} [CommRing R] [IsDomain R] {s : OAct R W L} {I J : Ideal R} {N : ℕ}

/-- `ι(β)` maps `E[N]` into `E[I]` for `β ∈ J` when `I J = (N)`. -/
lemma ι_mem_kerI_of_tors (hIJ : I * J = Ideal.span {(N : R)}) {β : R} (hβ : β ∈ J) {T : Pt W L}
    (hT : N • T = 0) : s.ι β T ∈ kerI s I := by
  refine mem_kerI.mpr fun γ hγ => ?_
  have hm : γ * β ∈ Ideal.span {(N : R)} := hIJ ▸ Ideal.mul_mem_mul hγ hβ
  obtain ⟨ε, hε⟩ := Ideal.mem_span_singleton'.mp hm
  calc s.ι γ (s.ι β T) = s.ι (γ * β) T := by rw [map_mul]; rfl
    _ = s.ι (ε * N) T := by rw [hε]
    _ = s.ι ε (s.ι (N : R) T) := by rw [map_mul]; rfl
    _ = 0 := by rw [s.natCast_apply, hT, map_zero]

/-- **(b3) Kernel ideals**: if `α` kills `E[I]` then `α ∈ I` (`I J = (N)`, `p ∤ N`); so `Ann(E[I]) = I`. -/
theorem mem_of_kills_kerI (hIJ : I * J = Ideal.span {(N : R)}) (hNF : (N : F) ≠ 0) {α : R}
    (hα : ∀ P ∈ kerI s I, s.ι α P = 0) : α ∈ I := by
  have hJ : Ideal.span {α} * J ≤ Ideal.span {(N : R)} := by
    rw [Ideal.span_singleton_mul_le_iff]
    intro β hβ
    have hker : ∀ T : Pt W L, N • T = 0 → s.ι (α * β) T = 0 := fun T hT => by
      rw [map_mul]; exact hα _ (ι_mem_kerI_of_tors hIJ hβ hT)
    obtain ⟨χ, hχ, he⟩ := endFq_div hNF (s.mem (α * β)) hker
    obtain ⟨z, rfl⟩ := s.surj _ hχ
    have h1 : α * β = N * z := s.inj (by rw [he, map_mul, map_natCast])
    rw [h1]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h2 : α * N ∈ I * Ideal.span {(N : R)} := by
    have h3 : Ideal.span {α} * Ideal.span {(N : R)} ≤ I * Ideal.span {(N : R)} := by
      calc Ideal.span {α} * Ideal.span {(N : R)} = I * (Ideal.span {α} * J) := by rw [← hIJ]; ring
        _ ≤ I * Ideal.span {(N : R)} := Ideal.mul_mono_right hJ
    exact h3 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self α) (Ideal.mem_span_singleton_self _))
  obtain ⟨z, hz, hzN⟩ := Ideal.mem_mul_span_singleton.mp h2
  rwa [← mul_right_cancel₀ (s.natCast_ne_zero hNF) hzN]

variable {W' : WeierstrassCurve F} [W'.IsElliptic] {φ : Pt W L →+ Pt W' L} {ψ : Pt W' L →+ Pt W L} {n : ℕ}

lemma exists_mul_γ (hq : IsQuot (kerI s I) φ ψ n) (hIJ : I * J = Ideal.span {(N : R)})
    (hNF : (N : F) ≠ 0) {γ : AddMonoid.End (Pt W' L)} (hγ : γ ∈ endFq W' L) {β : R} (hβ : β ∈ I) :
    ∃ a ∈ I, ιq hq a = ιq hq β * γ := by
  obtain ⟨Φβ, hΦβ⟩ := (mem_endRing).mp (mem_endFq.mp (s.mem β)).1
  obtain ⟨β', hβ', hβ'φ, hβ'f⟩ := hq.factor (W₁ := W) (α := (s.ι β : Pt W L →+ Pt W L))
    ⟨Φβ, fun S => hΦβ S⟩ (fun T hT => mem_kerI.mp hT β hβ)
  have hβfr := hβ'f (s.frob_comm β)
  obtain ⟨Γ, hΓ⟩ := (mem_endRing).mp (mem_endFq.mp hγ).1
  have hγf : ∀ Q, γ (RPLib.EllFq.frob W' L Q) = RPLib.EllFq.frob W' L (γ Q) := fun Q =>
    (DFunLike.congr_fun (mem_endFq.mp hγ).2 Q).symm
  have hiγ : IsIsog (W := W') (W' := W') (γ : Pt W' L →+ Pt W' L) := ⟨Γ, fun S => hΓ S⟩
  obtain ⟨E, hE⟩ := (hβ'.comp hiγ).comp hq.isog
  have hεmem : ((β'.comp (γ : Pt W' L →+ Pt W' L)).comp φ : AddMonoid.End (Pt W L)) ∈ endFq W L := by
    refine mem_endFq.mpr ⟨(mem_endRing).mpr ⟨E, fun S => hE S⟩, AddMonoidHom.ext fun P => ?_⟩
    show RPLib.EllFq.frob W L (β' (γ (φ P))) = β' (γ (φ (RPLib.EllFq.frob W L P)))
    rw [hq.frob, hγf, hβfr]
  obtain ⟨a, ha⟩ := s.surj _ hεmem
  have haI : a ∈ I := mem_of_kills_kerI hIJ hNF fun P hP => by
    rw [ha]
    show β' (γ (φ P)) = 0
    rw [(hq.ker P).mpr hP, map_zero, map_zero]
  have hιβ : ∀ Q, ιq hq β Q = φ (β' Q) := fun Q => by
    obtain ⟨R, rfl⟩ := hq.surj Q
    rw [ιq_spec, hβ'φ]
    try rfl
  refine ⟨a, haI, hq.ext_end fun P => ?_⟩
  show ιq hq a (φ P) = ιq hq β (γ (φ P))
  rw [ιq_spec, ha, hιβ]
  try rfl

/-- **(b4) `End_{F_q}(E/E[I]) = ι_I(O)`** (`I J = (N)`, `p ∤ N`). -/
theorem exists_ιq_eq (hq : IsQuot (kerI s I) φ ψ n) (hIJ : I * J = Ideal.span {(N : R)})
    (hNF : (N : F) ≠ 0) {γ : AddMonoid.End (Pt W' L)} (hγ : γ ∈ endFq W' L) : ∃ α, ιq hq α = γ := by
  let S : Ideal R :=
    { carrier := {x | ∃ y ∈ Ideal.span {(N : R)}, ιq hq y = ιq hq x * γ}
      add_mem' := by
        rintro x₁ x₂ ⟨y₁, hy₁, e₁⟩ ⟨y₂, hy₂, e₂⟩
        exact ⟨y₁ + y₂, add_mem hy₁ hy₂, by rw [map_add, map_add, e₁, e₂, add_mul]⟩
      zero_mem' := ⟨0, zero_mem _, by rw [map_zero, zero_mul]⟩
      smul_mem' := by
        rintro r x ⟨y, hy, e⟩
        exact ⟨r * y, Ideal.mul_mem_left _ r hy, by rw [smul_eq_mul, map_mul, map_mul, e, mul_assoc]⟩ }
  have hJI : J * I ≤ S := Ideal.mul_le.mpr fun j hj β hβ => by
    obtain ⟨a, ha, e⟩ := exists_mul_γ hq hIJ hNF hγ hβ
    show ∃ y ∈ Ideal.span {(N : R)}, ιq hq y = ιq hq (j * β) * γ
    refine ⟨j * a, ?_, by rw [map_mul, map_mul, e, mul_assoc]⟩
    rw [← hIJ, mul_comm I J]; exact Ideal.mul_mem_mul hj ha
  obtain ⟨y, hy, e⟩ : ∃ y ∈ Ideal.span {(N : R)}, ιq hq y = ιq hq (N : R) * γ :=
    hJI (by rw [mul_comm J I, hIJ]; exact Ideal.mem_span_singleton_self _)
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  refine ⟨z, ?_⟩
  rw [map_mul, map_natCast] at e
  have h0 : (γ - ιq hq z) * (N : AddMonoid.End (Pt W' L)) = 0 := by
    rw [sub_mul, ← Nat.cast_comm N γ, ← e, sub_self]
  have hN0 : (N : AddMonoid.End (Pt W' L)) ≠ 0 := natCast_end_ne_zero hNF
  exact (sub_eq_zero.mp (eq_zero_of_mul_eq_zero (natCast_mem (endRing W' L) N) hN0 h0)).symm

end KI

end RPLib.DWS


