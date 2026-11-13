-- Prove2me | Definitions.Def_RPLib_S1_Eigenbasis
-- name    : RPLib_S1_Eigenbasis
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:27:12.912205+00:00
-- url     : https://prove2.me/theorems/815c7509-d3dc-40db-9e2f-d8aea0651d56
-- title:
--   Simultaneous eigenbases for the good Hecke operators
-- statement:
--   Let $V$ be a subspace of $S_k(M,\chi)$ stable under all $T_p$ with $p \nmid M$. Then $V$ has a basis of simultaneous eigenvectors of $\{T_p : p\nmid M\}$, and $V$ is the sum of the joint eigenspaces. The proof is the spectral theorem for a commuting family of operators that are normal for the Petersson product, after a unitary rescaling that turns $\langle T_p x, y\rangle = \omega \langle x, T_p y\rangle$ with $|\omega| = 1$ into self-adjointness.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Theorem 5.5.4

import Mathlib
import Definitions.Def_RPLib_S1_Adjoint
import Definitions.Def_RPLib_S1_HeckeAlgebra
import Definitions.Def_RPLib_S1_FinDim

/-!
# S1-EIGEN: simultaneous eigenbases for the good-prime Hecke family

* Generic: a family of operators on a finite-dimensional complex inner product space that is symmetric on an
  invariant subspace `W` and commutes on `W` diagonalises simultaneously on `W`
  (`iSup_inf_iInf_eigenspace_eq`), also through a linear equivalence (`iSup_inf_iInf_eigenspace_eq_of_equiv`),
  and the *twisted* version `⟪T x, y⟫ = ω ⟪x, T y⟫`, `‖ω‖ = 1` (unitary rescaling `c • T`, `c² = ω`):
  `iSup_inf_iInf_eigenspace_eq_of_twisted`.
* Applied: every `V ≤ S_k(M, χ)` stable under all `T_p` (`p ∤ M`) is spanned by common eigenvectors of
  `{T_p : p ∤ M}` (`span_goodEigen_chi`), has a basis of such (`exists_goodEigen_basis_chi`,
  `exists_goodEigen_basis_chi'`), and `V = ⨆` of joint eigenspaces (`iSup_heckeTP_eigenspace_chi`).
  For `V ≤ S_k(Γ₁(M))` stable under all `T_p` (`p ∤ M`) and all `⟨d⟩`: `span_goodEigen_of_diamond`.
-/

set_option autoImplicit false

open scoped ComplexConjugate

namespace RP.Eigenbasis

/-! ## Generic linear algebra -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable {ι : Type*}

/-- **Simultaneous diagonalisation on an invariant subspace.** If `W` is stable under every `T i`, each `T i` is
symmetric on `W` and the `T i` commute on `W`, then `W` is the sum of its joint eigenspaces. -/
theorem iSup_inf_iInf_eigenspace_eq (W : Submodule ℂ E) (T : ι → Module.End ℂ E)
    (hW : ∀ i, ∀ x ∈ W, T i x ∈ W)
    (hS : ∀ i, ∀ x ∈ W, ∀ y ∈ W, inner ℂ (T i x) y = inner ℂ x (T i y))
    (hC : ∀ i j, ∀ x ∈ W, T i (T j x) = T j (T i x)) :
    ⨆ μ : ι → ℂ, (W ⊓ ⨅ i, Module.End.eigenspace (T i) (μ i)) = W := by
  let R : ι → Module.End ℂ W := fun i => (T i).restrict (hW i)
  have hRS : ∀ i, (R i).IsSymmetric := by
    intro i x y
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact hS i x x.2 y y.2
  have hRC : Pairwise (fun i j => Commute (R i) (R j)) := by
    intro i j _
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hC i j x x.2
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hRS hRC
  refine le_antisymm (iSup_le fun μ => inf_le_left) ?_
  calc W = Submodule.map W.subtype ⊤ := W.map_subtype_top.symm
    _ = Submodule.map W.subtype (⨆ μ : ι → ℂ, ⨅ i, Module.End.eigenspace (R i) (μ i)) := by rw [htop]
    _ = ⨆ μ : ι → ℂ, Submodule.map W.subtype (⨅ i, Module.End.eigenspace (R i) (μ i)) :=
        Submodule.map_iSup _ _
    _ ≤ ⨆ μ : ι → ℂ, (W ⊓ ⨅ i, Module.End.eigenspace (T i) (μ i)) := by
      refine iSup_mono fun μ => ?_
      rintro _ ⟨y, hy, rfl⟩
      refine Submodule.mem_inf.2 ⟨y.2, Submodule.mem_iInf _ |>.2 fun i => ?_⟩
      have h := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hy i)
      rw [Module.End.mem_eigenspace_iff]
      exact congrArg Subtype.val h

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The same, for operators on a vector space `V` identified with an inner product space by `e`. -/
theorem iSup_inf_iInf_eigenspace_eq_of_equiv (e : V ≃ₗ[ℂ] E) (W : Submodule ℂ V)
    (T : ι → Module.End ℂ V)
    (hW : ∀ i, ∀ x ∈ W, T i x ∈ W)
    (hS : ∀ i, ∀ x ∈ W, ∀ y ∈ W, inner ℂ (e (T i x)) (e y) = inner ℂ (e x) (e (T i y)))
    (hC : ∀ i j, ∀ x ∈ W, T i (T j x) = T j (T i x)) :
    ⨆ μ : ι → ℂ, (W ⊓ ⨅ i, Module.End.eigenspace (T i) (μ i)) = W := by
  let T' : ι → Module.End ℂ E := fun i =>
    (e : V →ₗ[ℂ] E) ∘ₗ T i ∘ₗ (e.symm : E →ₗ[ℂ] V)
  have hT' : ∀ i y, T' i y = e (T i (e.symm y)) := fun _ _ => rfl
  let W' : Submodule ℂ E := W.map (e : V →ₗ[ℂ] E)
  have memW' : ∀ y, y ∈ W' ↔ e.symm y ∈ W := fun _ => Submodule.mem_map_equiv W
  have hW' : ∀ i, ∀ y ∈ W', T' i y ∈ W' := by
    intro i y hy
    rw [memW', hT', e.symm_apply_apply]
    exact hW i _ ((memW' y).1 hy)
  have hS' : ∀ i, ∀ x ∈ W', ∀ y ∈ W', inner ℂ (T' i x) y = inner ℂ x (T' i y) := by
    intro i x hx y hy
    have h := hS i _ ((memW' x).1 hx) _ ((memW' y).1 hy)
    rw [e.apply_symm_apply, e.apply_symm_apply] at h
    rw [hT', hT']
    exact h
  have hC' : ∀ i j, ∀ y ∈ W', T' i (T' j y) = T' j (T' i y) := by
    intro i j y hy
    rw [hT', hT', hT', hT', e.symm_apply_apply, e.symm_apply_apply, hC i j _ ((memW' y).1 hy)]
  have h' := iSup_inf_iInf_eigenspace_eq W' T' hW' hS' hC'
  refine le_antisymm (iSup_le fun μ => inf_le_left) ?_
  intro v hv
  have hev : e v ∈ ⨆ μ : ι → ℂ, (W' ⊓ ⨅ i, Module.End.eigenspace (T' i) (μ i)) := by
    rw [h', memW', e.symm_apply_apply]
    exact hv
  have hm := Submodule.mem_map_of_mem (f := (e.symm : E →ₗ[ℂ] V)) hev
  rw [Submodule.map_iSup] at hm
  have hv' : (e.symm : E →ₗ[ℂ] V) (e v) = v := e.symm_apply_apply v
  rw [hv'] at hm
  refine SetLike.le_def.1 (iSup_mono fun μ => ?_) hm
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨hyW, hyE⟩ := Submodule.mem_inf.1 hy
  refine Submodule.mem_inf.2 ⟨(memW' y).1 hyW, Submodule.mem_iInf _ |>.2 fun i => ?_⟩
  have h := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hyE i)
  rw [hT'] at h
  rw [Module.End.mem_eigenspace_iff]
  show T i (e.symm y) = μ i • e.symm y
  calc T i (e.symm y) = e.symm (e (T i (e.symm y))) := (e.symm_apply_apply _).symm
    _ = e.symm (μ i • y) := by rw [h]
    _ = μ i • e.symm y := map_smul _ _ _

/-- A complex number of norm one has a square root of norm one, whose conjugate is its inverse. -/
theorem exists_sq_eq_of_norm_eq_one {ω : ℂ} (hω : ‖ω‖ = 1) :
    ∃ c : ℂ, c ^ 2 = ω ∧ c ≠ 0 ∧ conj c = c⁻¹ := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ω two_pos
  have hcn : ‖c‖ = 1 := by
    have h := congrArg norm hc
    rw [norm_pow, hω] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hcn
    exact zero_ne_one hcn
  exact ⟨c, hc, hc0, (Complex.inv_eq_conj hcn).symm⟩

/-- **Twisted version (unitary rescaling).** If `⟪T i x, y⟫ = ω i ⟪x, T i y⟫` on `W` with `‖ω i‖ = 1`, the same
conclusion holds: `c • T i` with `c² = ω i` is symmetric on `W`. This covers normal operators of the form
"adjoint = unimodular scalar times the operator" (e.g. `T_p^* = χ(p)⁻¹ T_p` on `S_k(M, χ)`). -/
theorem iSup_inf_iInf_eigenspace_eq_of_twisted (e : V ≃ₗ[ℂ] E) (W : Submodule ℂ V)
    (T : ι → Module.End ℂ V) (ω : ι → ℂ) (hω : ∀ i, ‖ω i‖ = 1)
    (hW : ∀ i, ∀ x ∈ W, T i x ∈ W)
    (hS : ∀ i, ∀ x ∈ W, ∀ y ∈ W, inner ℂ (e (T i x)) (e y) = ω i * inner ℂ (e x) (e (T i y)))
    (hC : ∀ i j, ∀ x ∈ W, T i (T j x) = T j (T i x)) :
    ⨆ μ : ι → ℂ, (W ⊓ ⨅ i, Module.End.eigenspace (T i) (μ i)) = W := by
  choose c hc hc0 hconj using fun i => exists_sq_eq_of_norm_eq_one (hω i)
  let T' : ι → Module.End ℂ V := fun i => c i • T i
  have hT' : ∀ i x, T' i x = c i • T i x := fun _ _ => rfl
  have hW' : ∀ i, ∀ x ∈ W, T' i x ∈ W := fun i x hx => by
    rw [hT']
    exact W.smul_mem _ (hW i x hx)
  have hS' : ∀ i, ∀ x ∈ W, ∀ y ∈ W, inner ℂ (e (T' i x)) (e y) = inner ℂ (e x) (e (T' i y)) := by
    intro i x hx y hy
    rw [hT', hT', map_smul, map_smul, inner_smul_left, inner_smul_right, hS i x hx y hy, ← mul_assoc,
      hconj, ← hc i, pow_two, ← mul_assoc, inv_mul_cancel₀ (hc0 i), one_mul]
  have hC' : ∀ i j, ∀ x ∈ W, T' i (T' j x) = T' j (T' i x) := by
    intro i j x hx
    rw [hT', hT', hT', hT', map_smul, map_smul, smul_smul, smul_smul, mul_comm (c i) (c j),
      hC i j x hx]
  have h' := iSup_inf_iInf_eigenspace_eq_of_equiv e W T' hW' hS' hC'
  refine le_antisymm (iSup_le fun μ => inf_le_left) (h'.ge.trans (iSup_le fun μ => ?_))
  refine le_iSup_of_le (fun i => (c i)⁻¹ * μ i) (inf_le_inf_left _ (iInf_mono fun i => ?_))
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [hT'] at hx
  calc T i x = (c i)⁻¹ • (c i • T i x) := by rw [smul_smul, inv_mul_cancel₀ (hc0 i), one_smul]
    _ = ((c i)⁻¹ * μ i) • x := by rw [hx, smul_smul]

/-- From the joint-eigenspace decomposition to a spanning set of common eigenvectors. -/
theorem span_eq_of_iSup_eq (W : Submodule ℂ V) (T : ι → Module.End ℂ V)
    (h : ⨆ μ : ι → ℂ, (W ⊓ ⨅ i, Module.End.eigenspace (T i) (μ i)) = W) :
    Submodule.span ℂ {x | x ∈ W ∧ ∀ i, ∃ c : ℂ, T i x = c • x} = W := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => hx.1) (h.ge.trans (iSup_le fun μ => ?_))
  intro x hx
  obtain ⟨hxW, hxE⟩ := Submodule.mem_inf.1 hx
  refine Submodule.subset_span ⟨hxW, fun i => ⟨μ i, ?_⟩⟩
  exact Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hxE i)

/-- A spanning set of vectors with a property `P` contains a linearly independent spanning subset of nonzero
vectors with `P`. -/
theorem exists_indep_of_span_eq (W : Submodule ℂ V) (P : V → Prop)
    (h : Submodule.span ℂ {x | x ∈ W ∧ P x} = W) :
    ∃ s : Set V, (∀ x ∈ s, x ∈ W ∧ x ≠ 0 ∧ P x) ∧ LinearIndependent ℂ ((↑) : s → V) ∧
      Submodule.span ℂ s = W := by
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℂ {x | x ∈ W ∧ P x}
  refine ⟨b, fun x hx => ⟨(hb hx).1, ?_, (hb hx).2⟩, hli, hspan.trans h⟩
  exact hli.ne_zero ⟨x, hx⟩

/-- `Basis`-typed form of `exists_indep_of_span_eq`. -/
theorem exists_basis_of_span_eq (W : Submodule ℂ V) (P : V → Prop)
    (h : Submodule.span ℂ {x | x ∈ W ∧ P x} = W) :
    ∃ (s : Set V) (b : Module.Basis s ℂ W), (∀ j : s, (b j : V) = j) ∧ ∀ x ∈ s, x ∈ W ∧ x ≠ 0 ∧ P x := by
  obtain ⟨s, hs, hli, hspan⟩ := exists_indep_of_span_eq W P h
  have hr : Submodule.span ℂ (Set.range ((↑) : s → V)) = W := by
    rw [Subtype.range_coe]
    exact hspan
  refine ⟨s, (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hr), fun j => ?_, hs⟩
  rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]

end Generic

/-! ## The good-prime Hecke family on `S_k(Γ₁(M))` -/

section Applied

open RamanujanPetersson RamanujanPetersson.Diamond RamanujanPetersson.Hecke RamanujanPetersson.HeckeAlgebra
open RP.Petersson CongruenceSubgroup

variable {M : ℕ}

variable (M) in
/-- The good primes `p ∤ M`. -/
abbrev GoodPrime : Type := {p : ℕ // p.Prime ∧ ¬ p ∣ M}

variable (M) in
/-- `S_k(Γ₁(M))` identified with its Petersson inner product space (identity on cusp forms). -/
def toPS (k : ℤ) : S1 M k ≃ₗ[ℂ] PeterssonSpace (Gamma1 M) k where
  toFun := PeterssonSpace.ofCuspForm
  invFun := PeterssonSpace.toCuspForm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable [NeZero M]

omit [NeZero M] in
theorem inner_toPS (k : ℤ) (f g : S1 M k) :
    inner ℂ (toPS M k f) (toPS M k g) = peterssonInner (Gamma1 M) k f g :=
  rfl

/-- `PeterssonSpace (Γ₁(M)) k` is finite-dimensional. -/
theorem finiteDimensional_PS (k : ℤ) : FiniteDimensional ℂ (PeterssonSpace (Gamma1 M) k) :=
  haveI := RamanujanPetersson.FinDim.finiteDimensional_cuspForm_Gamma1 M k
  LinearEquiv.finiteDimensional (toPS M k)

/-- `f` is a common eigenvector of every good-prime Hecke operator `T_p` (`p ∤ M`). -/
def IsGoodEigen (k : ℤ) (f : S1 M k) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → ∃ c : ℂ, heckeT p k f = c • f

theorem isGoodEigen_iff_heckeTP (k : ℤ) (f : S1 M k) :
    IsGoodEigen k f ↔ ∀ i : GoodPrime M, ∃ c : ℂ, heckeTP k i.1 f = c • f := by
  constructor
  · intro h i
    have : Fact i.1.Prime := ⟨i.2.1⟩
    rw [heckeTP_eq]
    exact h i.1 i.2.2
  · intro h p hp hpM
    rw [← heckeTP_eq]
    exact h ⟨p, hp.out, hpM⟩

omit [NeZero M] in
/-- `‖χ(p)⁻¹‖ = 1` for a good prime. -/
theorem norm_chi_inv_eq_one (χ : DirichletCharacter ℂ M) (i : GoodPrime M) :
    ‖(χ (i.1 : ZMod M))⁻¹‖ = 1 := by
  have h := χ.unit_norm_eq_one (ZMod.unitOfCoprime i.1 ((Nat.Prime.coprime_iff_not_dvd i.2.1).2 i.2.2))
  rw [ZMod.coe_unitOfCoprime] at h
  rw [norm_inv, h, inv_one]

/-- **Joint eigenspace decomposition.** Every `V ≤ S_k(M, χ)` stable under all `T_p` (`p ∤ M`) is the sum of its
joint eigenspaces for `{T_p : p ∤ M}`. -/
theorem iSup_heckeTP_eigenspace_chi {k : ℤ} (χ : DirichletCharacter ℂ M) (V : Submodule ℂ (S1 M k))
    (hV : V ≤ chiSubspace k χ)
    (hT : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → ∀ f ∈ V, heckeT p k f ∈ V) :
    ⨆ μ : GoodPrime M → ℂ, (V ⊓ ⨅ i, Module.End.eigenspace (heckeTP k i.1) (μ i)) = V := by
  have := finiteDimensional_PS (M := M) k
  refine iSup_inf_iInf_eigenspace_eq_of_twisted (toPS M k) V (fun i : GoodPrime M => heckeTP k i.1)
    (fun i => (χ (i.1 : ZMod M))⁻¹) (norm_chi_inv_eq_one χ) ?_ ?_ ?_
  · intro i f hf
    have : Fact i.1.Prime := ⟨i.2.1⟩
    show heckeTP k i.1 f ∈ V
    rw [heckeTP_eq]
    exact hT i.1 i.2.2 f hf
  · intro i f _ g hg
    have : Fact i.1.Prime := ⟨i.2.1⟩
    show inner ℂ (toPS M k (heckeTP k i.1 f)) (toPS M k g) =
      (χ (i.1 : ZMod M))⁻¹ * inner ℂ (toPS M k f) (toPS M k (heckeTP k i.1 g))
    rw [inner_toPS, inner_toPS, heckeTP_eq]
    exact RP.Adjoint.peterssonInner_heckeT_chi k i.2.2 f (hV hg)
  · intro i j f _
    show heckeTP k i.1 (heckeTP k j.1 f) = heckeTP k j.1 (heckeTP k i.1 f)
    exact LinearMap.congr_fun (heckeTP_commute k i.1 j.1).eq f

/-- **Spanning by common eigenvectors.** Every `V ≤ S_k(M, χ)` stable under all `T_p` (`p ∤ M`) is spanned by
common eigenvectors of `{T_p : p ∤ M}` lying in `V`. -/
theorem span_goodEigen_chi {k : ℤ} (χ : DirichletCharacter ℂ M) (V : Submodule ℂ (S1 M k))
    (hV : V ≤ chiSubspace k χ)
    (hT : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → ∀ f ∈ V, heckeT p k f ∈ V) :
    Submodule.span ℂ {f | f ∈ V ∧ IsGoodEigen k f} = V := by
  have h := span_eq_of_iSup_eq V _ (iSup_heckeTP_eigenspace_chi χ V hV hT)
  refine le_antisymm (Submodule.span_le.2 fun f hf => hf.1) (h.ge.trans (Submodule.span_mono ?_))
  rintro f ⟨hfV, hf⟩
  exact ⟨hfV, (isGoodEigen_iff_heckeTP k f).2 hf⟩

/-- **Eigenbasis.** Every `V ≤ S_k(M, χ)` stable under all `T_p` (`p ∤ M`) has a finite linearly independent
spanning set of nonzero common eigenvectors of `{T_p : p ∤ M}`. -/
theorem exists_goodEigen_basis_chi {k : ℤ} (χ : DirichletCharacter ℂ M) (V : Submodule ℂ (S1 M k))
    (hV : V ≤ chiSubspace k χ)
    (hT : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → ∀ f ∈ V, heckeT p k f ∈ V) :
    ∃ s : Set (S1 M k), s.Finite ∧ (∀ f ∈ s, f ∈ V ∧ f ≠ 0 ∧ IsGoodEigen k f) ∧
      LinearIndependent ℂ ((↑) : s → S1 M k) ∧ Submodule.span ℂ s = V := by
  have := RamanujanPetersson.FinDim.finiteDimensional_cuspForm_Gamma1 M k
  obtain ⟨s, hs, hli, hspan⟩ := exists_indep_of_span_eq V (IsGoodEigen k) (span_goodEigen_chi χ V hV hT)
  exact ⟨s, hli.setFinite, hs, hli, hspan⟩

/-- `Basis`-typed eigenbasis of `V ≤ S_k(M, χ)`. -/
theorem exists_goodEigen_basis_chi' {k : ℤ} (χ : DirichletCharacter ℂ M) (V : Submodule ℂ (S1 M k))
    (hV : V ≤ chiSubspace k χ)
    (hT : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → ∀ f ∈ V, heckeT p k f ∈ V) :
    ∃ (s : Set (S1 M k)) (b : Module.Basis s ℂ V), (∀ j : s, (b j : S1 M k) = j) ∧
      ∀ f ∈ s, f ∈ V ∧ f ≠ 0 ∧ IsGoodEigen k f :=
  exists_basis_of_span_eq V (IsGoodEigen k) (span_goodEigen_chi χ V hV hT)

/-- The whole space `S_k(M, χ)` is spanned by common eigenvectors of `{T_p : p ∤ M}`. -/
theorem span_goodEigen_chiSubspace (k : ℤ) (χ : DirichletCharacter ℂ M) :
    Submodule.span ℂ {f | f ∈ chiSubspace k χ ∧ IsGoodEigen k f} = chiSubspace k χ :=
  span_goodEigen_chi χ _ le_rfl fun _ _ _ _ hf => heckeT_mem_chiSubspace k hf

/-- **Without a fixed character.** Every `V ≤ S_k(Γ₁(M))` stable under all `T_p` (`p ∤ M`) and all `⟨d⟩` is
spanned by vectors of `V` that lie in some `S_k(M, χ)` and are common eigenvectors of `{T_p : p ∤ M}`. -/
theorem span_goodEigen_of_diamond {k : ℤ} (V : Submodule ℂ (S1 M k))
    (hT : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → ∀ f ∈ V, heckeT p k f ∈ V)
    (hD : ∀ d : (ZMod M)ˣ, ∀ f ∈ V, diamond k d f ∈ V) :
    Submodule.span ℂ
      {f | f ∈ V ∧ (∃ χ : DirichletCharacter ℂ M, f ∈ chiSubspace k χ) ∧ IsGoodEigen k f} = V := by
  refine le_antisymm (Submodule.span_le.2 fun f hf => hf.1) ?_
  intro f hf
  rw [← sum_proj k f]
  refine Submodule.sum_mem _ fun χ _ => ?_
  have hpV : proj k χ f ∈ V := by
    rw [proj_apply]
    exact V.smul_mem _ (V.sum_mem fun d _ => V.smul_mem _ (hD d f hf))
  have hVχ := span_goodEigen_chi χ (V ⊓ chiSubspace k χ) inf_le_right
    (fun p _ hpM g hg => Submodule.mem_inf.2
      ⟨hT p hpM g (Submodule.mem_inf.1 hg).1, heckeT_mem_chiSubspace k (Submodule.mem_inf.1 hg).2⟩)
  have hmem : proj k χ f ∈ V ⊓ chiSubspace k χ := Submodule.mem_inf.2 ⟨hpV, proj_mem k χ f⟩
  rw [← hVχ] at hmem
  refine Submodule.span_mono ?_ hmem
  rintro g ⟨hg, hge⟩
  obtain ⟨hgV, hgχ⟩ := Submodule.mem_inf.1 hg
  exact ⟨hgV, ⟨χ, hgχ⟩, hge⟩

end Applied

end RP.Eigenbasis


