-- Prove2me | Definitions.Def_CuspForm_Gamma1HeckeOperators
-- name    : CuspForm_Gamma1HeckeOperators
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/35b24ef0-4644-5eee-8832-5dea28c2e513
-- title:
--   Diamond and Hecke operators on cusp forms for Γ1​(M)
-- statement:
--   Fix a level $M$ and an integer weight $k$, and work with Mathlib's space `CuspForm (Γ₁ℝ M) k` of cusp forms for the image of $\Gamma_1(M)\le \mathrm{SL}_2(\mathbb Z)$ in $\mathrm{GL}_2(\mathbb R)$, with the weight-$k$ slash action. The predicate [`CuspForm.IsDiamondLift M d γ`](../def/CuspForm_Gamma1HeckeOperators.html#L469) says that $\gamma\in\Gamma_0(M)$ and $\gamma_{11}\equiv d \pmod M$ (indices $0,1$ in Lean); such a $\gamma$ exists precisely when $d$ is coprime to $M$. For $\gamma\in\Gamma_0(M)$, `slashOfMemGamma0` is the cusp form with underlying function $f\mid_k\gamma$ — legitimate because conjugation by $\gamma$ preserves $\Gamma_1(M)$ — and `slashLinOfMemGamma0` packages this as a $\mathbb C$-linear endomorphism. The diamond operator `diamondLinOne M k d` is defined by cases: if $d$ admits a diamond lift it is $f\mapsto f\mid_k\gamma$ for a chosen lift, and otherwise it is the identity; the value is independent of the lift, so $\langle d\rangle f=f\mid_k\gamma$ for every diamond lift $\gamma$ of $d$, $\langle d\rangle=\mathrm{id}$ when $\gcd(d,M)\neq 1$, and $\langle 1\rangle=\mathrm{id}$.
--
--   For a prime $\ell$ with $\ell\nmid M$, `heckeTOne` is the cusp form $\sum_{j<\ell} f\mid_k\begin{pmatrix}1&j\\0&\ell\end{pmatrix}+(\langle\ell\rangle f)\mid_k\begin{pmatrix}\ell&0\\0&1\end{pmatrix}$, i.e. `heckeU k ℓ ⇑f` plus the slash of $\langle\ell\rangle f$ by `heckeDiagMatrix ℓ`, and `heckeTLinOne` is the resulting $\mathbb C$-linear endomorphism of the space of cusp forms. The structure fields of `heckeTOne` carry the three proofs that this function is again a cusp form: $\Gamma_1(M)$-invariance, holomorphy, and vanishing at the cusps.
--
--   The `Gamma1Hecke` namespace supplies these proofs. The $\ell+1$ coset representatives are indexed by $\mathbb P^1(\mathbb Z/\ell)$ via `heckeRep` ($\infty\mapsto\mathrm{diag}(\ell,1)$, $j\mapsto\begin{pmatrix}1&j\\0&\ell\end{pmatrix}$), with `wt N p` recording the determinant weight ($\infty\mapsto p$, $j\mapsto 1$ in $\mathbb Z/N$), `lift σ` inserting a diamond lift at $\infty$, and `redMatrix p g` the reduction $\begin{pmatrix}d&b\\c&a\end{pmatrix}$ mod $p$ of $g\in\mathrm{SL}_2(\mathbb Z)$ acting on $\mathbb P^1(\mathbb Z/p)$. The central commutation lemma produces, for $g\in\Gamma_0(M)$ and each $x$, an element $g'\in\Gamma_0(M)$ with a prescribed bottom row congruence and $\mathrm{rep}(x)\,g=g'\,\mathrm{rep}(\mathrm{red}(g)x)$; summing over $\mathbb P^1(\mathbb Z/\ell)$ gives invariance under $\Gamma_1(M)$ and the transformation rule under $\Gamma_0(M)$. Cuspidality uses that the matrices are rational, so they permute the cusps of an arithmetic subgroup.
--
--   **Relation to Mathlib.** Mathlib provides the space `CuspForm`, the congruence subgroups `Gamma0`/`Gamma1`, the slash action on $\mathrm{GL}_2(\mathbb R)$ and `CuspForm.translate`, but no diamond or Hecke operators on these spaces; the operators here are the project's own, built on the project's `heckeU`, `heckeMatrix` and `heckeDiagMatrix`.
--
--   **Where it is used.** These are the weight-$k$, level-$\Gamma_1(M)$ Hecke and diamond operators with nebentypus, used to compare the action on cusp forms with the action by correspondences on $J_1(M)$ in the Eichler–Shimura relation that attaches Galois representations to modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CuspForm.Gamma1Hecke

open Matrix.SpecialLinearGroup UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm OnePoint Manifold

theorem mdifferentiable_heckeU {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (k : ℤ) (p : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeU k p f) := by
  rw [heckeU_def]
  induction (Finset.range p) using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact mdifferentiable_const (c := (0 : ℂ))
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hf.slash k _).add ih

def heckeMatrixQ (p j : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (p : ℚ)]
    (by rw [Matrix.det_fin_two_of]; simpa using hp)

def heckeDiagMatrixQ (p : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(p : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simpa using hp)

theorem map_heckeMatrixQ {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    (heckeMatrixQ p j hp).map (Rat.castHom ℝ) = heckeMatrix p j := by
  apply Units.ext
  rw [val_heckeMatrix hp]
  change ((heckeMatrixQ p j hp : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) = _
  unfold heckeMatrixQ
  ext a b; fin_cases a <;> fin_cases b <;> simp

theorem map_heckeDiagMatrixQ {p : ℕ} (hp : p ≠ 0) :
    (heckeDiagMatrixQ p hp).map (Rat.castHom ℝ) = heckeDiagMatrix p := by
  apply Units.ext
  rw [val_heckeDiagMatrix hp]
  change ((heckeDiagMatrixQ p hp : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) = _
  unfold heckeDiagMatrixQ
  ext a b; fin_cases a <;> fin_cases b <;> simp

theorem isCusp_smul_map {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (g : GL (Fin 2) ℚ) :
    IsCusp (g.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  exact ⟨g • c₀, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem isZeroAt_slash_map {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsZeroAt (⇑f ∣[k] g.map (Rat.castHom ℝ)) k := by
  refine OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f ?_)
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact isCusp_smul_map hc g

theorem isZeroAt_zero {c : OnePoint ℝ} {k : ℤ} : c.IsZeroAt (0 : ℍ → ℂ) k := fun g _ => by
  rw [SlashAction.zero_slash]
  exact Filter.zero_zeroAtFilter _

theorem isZeroAt_finset_sum {ι : Type*} {c : OnePoint ℝ} {k : ℤ} (s : Finset ι) (G : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsZeroAt (G i) k) : c.IsZeroAt (∑ i ∈ s, G i) k :=
  Finset.sum_induction G (fun H => c.IsZeroAt H k) (fun _ _ ha hb => ha.add hb) isZeroAt_zero h

theorem isZeroAt_heckeU {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) {p : ℕ} (hp : p ≠ 0)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsZeroAt (heckeU k p ⇑f) k := by
  rw [heckeU_def]
  refine isZeroAt_finset_sum _ _ fun j _ => ?_
  rw [← map_heckeMatrixQ hp j]
  exact isZeroAt_slash_map f _ hc

theorem isZeroAt_slash_heckeDiagMatrix {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) {p : ℕ} (hp : p ≠ 0)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsZeroAt (⇑f ∣[k] heckeDiagMatrix p) k := by
  rw [← map_heckeDiagMatrixQ hp]
  exact isZeroAt_slash_map f _ hc

theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

attribute [local simp] mapGL_apply

theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

section commutation

variable {p : ℕ} (hp : p ≠ 0)
include hp

theorem heckeMatrix_mul_of_eq (g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ)
    (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧ g' 1 1 = g 1 1 - g 1 0 * j' ∧
      heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0 + j * g 1 0, e; p * g 1 0, g 1 1 - g 1 0 * j'], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 1 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

theorem heckeMatrix_mul_of_eq' (g : SL(2, ℤ)) (j : ℕ) (e : ℤ)
    (he : g 0 0 + j * g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧ g' 1 1 = p * g 1 1 ∧
      heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![e, g 0 1 + j * g 1 1; g 1 0, p * g 1 1], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 1 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

theorem heckeDiagMatrix_mul_of_eq (g : SL(2, ℤ)) (j' : ℕ) (e : ℤ)
    (he : g 1 1 = g 1 0 * j' + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧ g' 1 1 = e ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![p * g 0 0, g 0 1 - g 0 0 * j'; g 1 0, e], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 0 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

theorem heckeDiagMatrix_mul_of_eq' (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = e ∧ g' 1 1 = g 1 1 ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0, p * g 0 1; e, g 1 1], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 0 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

end commutation

section reindex

variable {p : ℕ} [NeZero p]

theorem sum_range_eq_sum_zmod {A : Type*} [AddCommMonoid A] (G : ℕ → A) :
    ∑ j ∈ Finset.range p, G j = ∑ x : ZMod p, G x.val := by
  refine Finset.sum_nbij' (fun j : ℕ ↦ (j : ZMod p)) (fun x : ZMod p ↦ x.val)
    (fun _ _ ↦ Finset.mem_univ _) (fun x _ ↦ Finset.mem_range.mpr x.val_lt) (fun j hj ↦ ?_)
    (fun x _ ↦ ?_) (fun j hj ↦ ?_)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · exact ZMod.natCast_zmod_val x
  · rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

theorem heckeU_eq_sum_zmod (k : ℤ) (f : ℍ → ℂ) :
    heckeU k p f = ∑ x : ZMod p, f ∣[k] heckeMatrix p x.val := by
  rw [heckeU_def]
  exact sum_range_eq_sum_zmod _

end reindex

section reps

variable {p : ℕ}

def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeMatrix p j.val)

@[simp] theorem heckeRep_infty : heckeRep p ∞ = heckeDiagMatrix p := rfl

@[simp] theorem heckeRep_coe (j : ZMod p) : heckeRep p j = heckeMatrix p j.val := rfl

def wt (N p : ℕ) (x : OnePoint (ZMod p)) : ZMod N := x.elim (p : ZMod N) (fun _ => 1)

@[simp] theorem wt_infty {N : ℕ} : wt N p ∞ = (p : ZMod N) := rfl

@[simp] theorem wt_coe {N : ℕ} (j : ZMod p) : wt N p j = 1 := rfl

theorem isUnit_wt {N : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (x : OnePoint (ZMod p)) :
    IsUnit (wt N p x) := by
  induction x using OnePoint.rec with
  | infty => exact ZMod.isUnit_prime_of_not_dvd hp hpN
  | coe j => exact isUnit_one

variable {N : ℕ}

def lift (σ : SL(2, ℤ)) (x : OnePoint (ZMod p)) : SL(2, ℤ) := x.elim σ (fun _ => 1)

@[simp] theorem lift_infty (σ : SL(2, ℤ)) : lift (p := p) σ ∞ = σ := rfl

@[simp] theorem lift_coe (σ : SL(2, ℤ)) (j : ZMod p) : lift σ (j : OnePoint (ZMod p)) = 1 := rfl

theorem lift_mem (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (x : OnePoint (ZMod p)) :
    lift σ x ∈ CongruenceSubgroup.Gamma0 N := by
  induction x using OnePoint.rec with
  | infty => exact hσ
  | coe j => exact one_mem _

theorem lift_apply_one_one (σ : SL(2, ℤ)) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (x : OnePoint (ZMod p)) : (((lift σ x) 1 1 : ℤ) : ZMod N) = wt N p x := by
  induction x using OnePoint.rec with
  | infty => exact hσp
  | coe j => simp

theorem d_mul {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ CongruenceSubgroup.Gamma0 N)
    (h₂ : γ₂ ∈ CongruenceSubgroup.Gamma0 N) :
    (((γ₁ * γ₂) 1 1 : ℤ) : ZMod N) = ((γ₁ 1 1 : ℤ) : ZMod N) * ((γ₂ 1 1 : ℤ) : ZMod N) := by
  have := map_mul (CongruenceSubgroup.Gamma0Map N) ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩
  exact this

theorem det_mod (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using CongruenceSubgroup.Gamma0_mem.mp hγ
  have := congrArg (Int.cast : ℤ → ZMod N) (det_eq γ)
  push_cast at this
  rw [hc] at this
  linear_combination this

theorem mem_Gamma1_of_d_eq_one {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (hd : ((γ 1 1 : ℤ) : ZMod N) = 1) : γ ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]
  have ha : ((γ 0 0 : ℤ) : ZMod N) = 1 := by
    have := det_mod γ hγ; rw [hd, mul_one] at this; exact this
  exact ⟨by simpa using ha, by simpa using hd, by simpa using CongruenceSubgroup.Gamma0_mem.mp hγ⟩

end reps

section heckeT

variable {p : ℕ} [Fact p.Prime]

variable (p) in

def redMatrix (g : SL(2, ℤ)) : GL (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((g 1 1 : ℤ) : ZMod p), ((g 0 1 : ℤ) : ZMod p); ((g 1 0 : ℤ) : ZMod p), ((g 0 0 : ℤ) : ZMod p)]
    (by
      have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
      push_cast at this
      rw [Matrix.det_fin_two_of,
        show ((g 1 1 : ℤ) : ZMod p) * ((g 0 0 : ℤ) : ZMod p) - ((g 0 1 : ℤ) : ZMod p) * ((g 1 0 : ℤ) : ZMod p)
          = 1 by linear_combination this]
      exact one_ne_zero)

@[simp] theorem redMatrix_apply_zero_zero (g : SL(2, ℤ)) :
    redMatrix p g 0 0 = ((g 1 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[simp] theorem redMatrix_apply_zero_one (g : SL(2, ℤ)) :
    redMatrix p g 0 1 = ((g 0 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[simp] theorem redMatrix_apply_one_zero (g : SL(2, ℤ)) :
    redMatrix p g 1 0 = ((g 1 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[simp] theorem redMatrix_apply_one_one (g : SL(2, ℤ)) :
    redMatrix p g 1 1 = ((g 0 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

theorem heckeRep_mul {N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N)
    (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧
      ((g' 1 1 : ℤ) : ZMod N) * wt N p x = ((g 1 1 : ℤ) : ZMod N) * wt N p (redMatrix p g • x) ∧
      heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hgC' : ((g 1 0 : ℤ) : ZMod N) = 0 := by simpa using CongruenceSubgroup.Gamma0_mem.mp hg
  have hgN : (N : ℤ) ∣ g 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hgC'
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : ((g 1 0 : ℤ) : ZMod p) = 0
    ·
      rw [if_pos (by simpa using hc), heckeRep_infty]
      obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
      obtain ⟨g', hg', hd', hmul⟩ := heckeDiagMatrix_mul_of_eq' hp g e he
      refine ⟨g', ?_, ?_, hmul⟩
      · rw [hg']
        have hcop : IsCoprime (N : ℤ) (p : ℤ) :=
          Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN).symm
        exact hcop.dvd_of_dvd_mul_left (he ▸ hgN)
      · rw [hd', wt_infty]
    ·
      rw [if_neg (by simpa using hc), heckeRep_infty, heckeRep_coe]
      set y : ZMod p := redMatrix p g 0 0 / redMatrix p g 1 0 with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 1 1 - g 1 0 * y.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, hy, redMatrix_apply_zero_zero, redMatrix_apply_one_zero,
          mul_div_cancel₀ _ hc, sub_self]
      obtain ⟨g', hg', hd', hmul⟩ := heckeDiagMatrix_mul_of_eq hp g y.val e (by linear_combination he)
      refine ⟨g', hg' ▸ hgN, ?_, hmul⟩
      rw [hd', wt_infty, wt_coe]
      have : ((g 1 1 : ℤ) : ZMod N) = ((g 1 0 : ℤ) : ZMod N) * (y.val : ℤ) + (p : ℤ) * e := by
        have := congrArg (Int.cast : ℤ → ZMod N)
          (show g 1 1 = g 1 0 * y.val + p * e by linear_combination he)
        push_cast at this ⊢
        exact this
      rw [hgC', zero_mul, zero_add] at this
      push_cast at this
      rw [mul_one, mul_comm, this]
  | coe j =>
    rw [OnePoint.smul_some_eq_ite]
    by_cases h : redMatrix p g 1 0 * j + redMatrix p g 1 1 = 0
    ·
      rw [if_pos h, heckeRep_infty, heckeRep_coe]
      rw [redMatrix_apply_one_zero, redMatrix_apply_one_one] at h
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 0 + j.val * g 1 0 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val]
        linear_combination h
      obtain ⟨g', hg', hd', hmul⟩ := heckeMatrix_mul_of_eq' hp g j.val e he
      refine ⟨g', hg' ▸ hgN, ?_, hmul⟩
      rw [hd', wt_infty, wt_coe, mul_one]
      push_cast
      rw [mul_comm]
    ·
      rw [if_neg h, heckeRep_coe, heckeRep_coe]
      set y : ZMod p := (redMatrix p g 0 0 * j + redMatrix p g 0 1) /
        (redMatrix p g 1 0 * j + redMatrix p g 1 1) with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 1 + j.val * g 1 1 - y.val * (g 0 0 + j.val * g 1 0) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
          show ((g 0 0 : ℤ) : ZMod p) + j * ((g 1 0 : ℤ) : ZMod p)
            = redMatrix p g 1 0 * j + redMatrix p g 1 1 by
              rw [redMatrix_apply_one_zero, redMatrix_apply_one_one]; ring,
          hy, div_mul_cancel₀ _ h, redMatrix_apply_zero_zero, redMatrix_apply_zero_one]
        ring
      obtain ⟨g', hg', hd', hmul⟩ :=
        heckeMatrix_mul_of_eq hp g j.val y.val e (by linear_combination he)
      refine ⟨g', hg' ▸ dvd_mul_of_dvd_right hgN _, ?_, hmul⟩
      rw [hd', wt_coe, wt_coe, mul_one, mul_one]
      push_cast
      rw [hgC', zero_mul, sub_zero]

variable {N : ℕ} (k : ℤ)

theorem sum_eq (f : ℍ → ℂ) (σ : SL(2, ℤ)) :
    heckeU k p f + (f ∣[k] mapGL ℝ σ) ∣[k] heckeDiagMatrix p
      = ∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x) := by
  rw [heckeU_eq_sum_zmod, add_comm, ← SlashAction.slash_mul]
  refine Eq.trans ?_
    (Fintype.sum_option (fun x : OnePoint (ZMod p) ↦ f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x))).symm
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  change f ∣[k] heckeMatrix p j.val = f ∣[k] (mapGL ℝ (lift σ (j : OnePoint (ZMod p))) * heckeRep p j)
  rw [lift_coe, map_one, one_mul, heckeRep_coe]

theorem isUnit_d {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    IsUnit ((γ 1 1 : ℤ) : ZMod N) :=
  IsUnit.of_mul_eq_one_right _ (det_mod γ hγ)

theorem sum_slash_mapGL_of_mem_Gamma0 (hpN : ¬ p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    (∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x)) ∣[k] (mapGL ℝ g)
      = ∑ x : OnePoint (ZMod p), (f ∣[k] mapGL ℝ g) ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x) := by
  rw [SlashAction.sum_slash]
  calc ∑ x : OnePoint (ZMod p), (f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x)) ∣[k] mapGL ℝ g
      = ∑ x : OnePoint (ZMod p), (f ∣[k] mapGL ℝ g) ∣[k] (mapGL ℝ (lift σ (redMatrix p g • x))
          * heckeRep p (redMatrix p g • x)) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨g', hg', hd', hmul⟩ := heckeRep_mul hpN g hg x
        have hg'N : g' ∈ CongruenceSubgroup.Gamma0 N :=
          CongruenceSubgroup.Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hg')

        set D : SL(2, ℤ) := lift σ x * g' * (lift σ (redMatrix p g • x))⁻¹ * g⁻¹ with hD
        have hDmem0 : D ∈ CongruenceSubgroup.Gamma0 N :=
          mul_mem (mul_mem (mul_mem (lift_mem σ hσ x) hg'N) (inv_mem (lift_mem σ hσ _))) (inv_mem hg)
        have hDd : ((D 1 1 : ℤ) : ZMod N) = 1 := by
          have hprod : D * g * lift σ (redMatrix p g • x) = lift σ x * g' := by
            rw [hD, inv_mul_cancel_right, inv_mul_cancel_right]
          have h1 : (((D * g * lift σ (redMatrix p g • x)) 1 1 : ℤ) : ZMod N)
              = (((lift σ x * g') 1 1 : ℤ) : ZMod N) :=
            congrArg (fun γ : SL(2, ℤ) => ((γ 1 1 : ℤ) : ZMod N)) hprod
          rw [d_mul (mul_mem hDmem0 hg) (lift_mem σ hσ _), d_mul hDmem0 hg,
            d_mul (lift_mem σ hσ x) hg'N, lift_apply_one_one σ hσp, lift_apply_one_one σ hσp,
            mul_comm (wt N p x), hd', mul_assoc] at h1
          have hu : IsUnit (((g 1 1 : ℤ) : ZMod N) * wt N p (redMatrix p g • x)) :=
            (isUnit_d hg).mul (isUnit_wt Fact.out hpN _)
          exact hu.mul_left_injective (h1.trans (one_mul _).symm)
        have hDmem : D ∈ CongruenceSubgroup.Gamma1 N := mem_Gamma1_of_d_eq_one hDmem0 hDd
        have hfactor : mapGL ℝ (lift σ x) * heckeRep p x * mapGL ℝ g
            = mapGL ℝ D * (mapGL ℝ g
              * (mapGL ℝ (lift σ (redMatrix p g • x)) * heckeRep p (redMatrix p g • x))) := by
          rw [mul_assoc, hmul, ← mul_assoc, ← map_mul, hD, ← mul_assoc, ← mul_assoc, ← map_mul,
            ← map_mul, inv_mul_cancel_right, inv_mul_cancel_right]
        rw [← SlashAction.slash_mul, hfactor, SlashAction.slash_mul,
          hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hDmem), SlashAction.slash_mul]
    _ = ∑ x : OnePoint (ZMod p), (f ∣[k] mapGL ℝ g) ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x) :=
        Equiv.sum_comp (MulAction.toPerm (redMatrix p g))
          (fun x ↦ (f ∣[k] mapGL ℝ g) ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x))

theorem sum_slash_mapGL (hpN : ¬ p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma1 N) :
    (∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x)) ∣[k] (mapGL ℝ g)
      = ∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x) := by
  rw [sum_slash_mapGL_of_mem_Gamma0 k hpN f hf σ hσ hσp g (CongruenceSubgroup.Gamma1_in_Gamma0 N hg),
    hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hg)]

end heckeT

theorem heckeU_add_slash_heckeDiagMatrix_slash
    {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (γ : GL (Fin 2) ℝ)
    (hγ : γ ∈ ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (heckeU k p f + (f ∣[k] (mapGL ℝ σ)) ∣[k] heckeDiagMatrix p) ∣[k] γ
      = heckeU k p f + (f ∣[k] (mapGL ℝ σ)) ∣[k] heckeDiagMatrix p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, rfl⟩ := hγ
  rw [sum_eq k f σ]
  exact sum_slash_mapGL k hpN f hf σ hσ hσp g hg

theorem heckeU_add_slash_heckeDiagMatrix_slash_of_mem_Gamma0
    {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    (heckeU k p f + (f ∣[k] (mapGL ℝ σ)) ∣[k] heckeDiagMatrix p) ∣[k] (mapGL ℝ g)
      = heckeU k p (f ∣[k] (mapGL ℝ g))
        + ((f ∣[k] (mapGL ℝ g)) ∣[k] (mapGL ℝ σ)) ∣[k] heckeDiagMatrix p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [sum_eq k f σ, sum_eq k (f ∣[k] mapGL ℝ g) σ]
  exact sum_slash_mapGL_of_mem_Gamma0 k hpN f hf σ hσ hσp g hg

end CuspForm.Gamma1Hecke

open CongruenceSubgroup ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace CuspForm

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀ℝ" M => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Lifts

variable (M : ℕ)

def IsDiamondLift (d : ℕ) (γ : SL(2, ℤ)) : Prop :=
  γ ∈ Gamma0 M ∧ ((γ 1 1 : ℤ) : ZMod M) = (d : ZMod M)

variable {M}

theorem exists_isDiamondLift_of_coprime {d : ℕ} (h : Nat.Coprime d M) :
    ∃ γ : SL(2, ℤ), IsDiamondLift M d γ := by
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 h : IsCoprime (d : ℤ) (M : ℤ))
  refine ⟨⟨!![u, -v; (M : ℤ), (d : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination huv
  · simp [Gamma0_mem]
  · simp

theorem IsDiamondLift.coprime {d : ℕ} {γ : SL(2, ℤ)} (h : IsDiamondLift M d γ) : Nat.Coprime d M := by
  have hdet := Matrix.det_fin_two γ.1
  rw [γ.2] at hdet
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.1 h.1
  have h1 : ((γ 0 0 : ℤ) : ZMod M) * (d : ZMod M) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod M)) hdet
    simp only [Int.cast_one, Int.cast_sub, Int.cast_mul, hc, mul_zero, sub_zero, h.2] at this
    exact this.symm
  exact (ZMod.isUnit_iff_coprime d M).1 (IsUnit.of_mul_eq_one_right _ h1)

theorem conj_mem_Gamma1 {γ x : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hx : x ∈ Gamma1 M) :
    γ * x * γ⁻¹ ∈ Gamma1 M := by
  have hx0 : x ∈ Gamma0 M := Gamma1_in_Gamma0 M hx
  have hx' : (⟨x, hx0⟩ : Gamma0 M) ∈ Gamma1' M := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem M x).1 hx
  haveI : (Gamma1' M).Normal := MonoidHom.normal_ker _
  have hc : (⟨γ, hγ⟩ : Gamma0 M) * ⟨x, hx0⟩ * (⟨γ, hγ⟩ : Gamma0 M)⁻¹ ∈ Gamma1' M :=
    Subgroup.Normal.conj_mem inferInstance _ hx' _
  rw [Gamma1_to_Gamma0_mem] at hc
  exact (Gamma1_mem M _).2 hc

theorem mem_coe_Gamma1_iff (x : GL (Fin 2) ℝ) :
    x ∈ (Γ₁ℝ M) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 M ∧ (Matrix.SpecialLinearGroup.mapGL ℝ γ) = x :=
  Subgroup.mem_map

open ConjAct Pointwise in

theorem toConjAct_inv_smul_coe_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ • (Γ₁ℝ M) = (Γ₁ℝ M) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul]
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := (mem_coe_Gamma1_iff _).1 h
    have hx : x = Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹ * Matrix.SpecialLinearGroup.mapGL ℝ y
        * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
      rw [hyx, map_inv]; group
    have hmem := conj_mem_Gamma1 (Subgroup.inv_mem _ hγ) hy
    rw [inv_inv] at hmem
    rw [hx, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ hmem
  · intro h
    obtain ⟨y, hy, rfl⟩ := (mem_coe_Gamma1_iff _).1 h
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (conj_mem_Gamma1 hγ hy)

end Lifts

section Diamond

variable (M : ℕ) (k : ℤ)

def slashOfMemGamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (f : CuspForm (Γ₁ℝ M) k) :
    CuspForm (Γ₁ℝ M) k :=
  (CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ γ)).copy (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)) rfl
    (toConjAct_inv_smul_coe_Gamma1 hγ).symm

@[simp] theorem coe_slashOfMemGamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(slashOfMemGamma0 M k hγ f) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := rfl

def slashLinOfMemGamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    CuspForm (Γ₁ℝ M) k →ₗ[ℂ] CuspForm (Γ₁ℝ M) k where
  toFun := slashOfMemGamma0 M k hγ
  map_add' f g := DFunLike.coe_injective <| by
    simp only [coe_slashOfMemGamma0, CuspForm.coe_add, SlashAction.add_slash]
  map_smul' c f := DFunLike.coe_injective <| by
    simp only [coe_slashOfMemGamma0, CuspForm.IsGLPos.coe_smul, RingHom.id_apply]
    exact ModularForm.SL_smul_slash k γ (⇑f) c

@[simp] theorem coe_slashLinOfMemGamma0_apply {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M)
    (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(slashLinOfMemGamma0 M k hγ f) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := rfl

theorem slash_eq_slash_of_isDiamondLift {d : ℕ} {γ γ' : SL(2, ℤ)} (hγ : IsDiamondLift M d γ)
    (hγ' : IsDiamondLift M d γ') (f : CuspForm (Γ₁ℝ M) k) :
    ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ') := by

  have hmem : γ' * γ⁻¹ ∈ Gamma1 M := by
    have hd := Matrix.det_fin_two γ.1
    rw [γ.2] at hd
    have hd' := Matrix.det_fin_two γ'.1
    rw [γ'.2] at hd'
    have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.1 hγ.1
    have hc' : ((γ' 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.1 hγ'.1
    have hδ : ((γ 1 1 : ℤ) : ZMod M) = d := hγ.2
    have hδ' : ((γ' 1 1 : ℤ) : ZMod M) = d := hγ'.2
    have ha : ((γ 0 0 : ℤ) : ZMod M) * d = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod M)) hd
      simp only [Int.cast_one, Int.cast_sub, Int.cast_mul, hc, mul_zero, sub_zero, hδ] at this
      exact this.symm
    have ha' : ((γ' 0 0 : ℤ) : ZMod M) * d = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod M)) hd'
      simp only [Int.cast_one, Int.cast_sub, Int.cast_mul, hc', mul_zero, sub_zero, hδ'] at this
      exact this.symm
    rw [Gamma1_mem, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_add, Int.cast_mul,
      Int.cast_neg, hc, hc', hδ, hδ', neg_zero, mul_zero, zero_mul, add_zero, zero_add, mul_neg]
    refine ⟨?_, ?_, trivial⟩
    · simpa only [mul_comm] using ha'
    · linear_combination ha
  have hinv := SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hmem)
  calc ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)
        = (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (γ' * γ⁻¹))) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := by rw [hinv]
      _ = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ') := by
          rw [← SlashAction.slash_mul, ← map_mul, inv_mul_cancel_right]

open Classical in

def diamondLinOne (d : ℕ) : CuspForm (Γ₁ℝ M) k →ₗ[ℂ] CuspForm (Γ₁ℝ M) k :=
  if h : ∃ γ : SL(2, ℤ), IsDiamondLift M d γ then slashLinOfMemGamma0 M k h.choose_spec.1
  else LinearMap.id

variable {M k}

theorem coe_diamondLinOne_apply {d : ℕ} {γ : SL(2, ℤ)} (hγ : IsDiamondLift M d γ)
    (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(diamondLinOne M k d f) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := by
  have h : ∃ γ : SL(2, ℤ), IsDiamondLift M d γ := ⟨γ, hγ⟩
  rw [diamondLinOne, dif_pos h, coe_slashLinOfMemGamma0_apply]
  exact slash_eq_slash_of_isDiamondLift M k h.choose_spec hγ f

theorem coe_diamondLinOne_apply' {d : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M)
    (hγd : ((γ 1 1 : ℤ) : ZMod M) = (d : ZMod M)) (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(diamondLinOne M k d f) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) :=
  coe_diamondLinOne_apply ⟨hγ, hγd⟩ f

theorem diamondLinOne_apply_apply {d : ℕ} {γ : SL(2, ℤ)} (hγ : IsDiamondLift M d γ)
    (f : CuspForm (Γ₁ℝ M) k) (τ : ℍ) :
    diamondLinOne M k d f τ = (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)) τ := by
  rw [coe_diamondLinOne_apply hγ]

theorem diamondLinOne_of_not {d : ℕ} (h : ¬ ∃ γ : SL(2, ℤ), IsDiamondLift M d γ) :
    diamondLinOne M k d = LinearMap.id := by
  rw [diamondLinOne, dif_neg h]

theorem diamondLinOne_of_not_coprime {d : ℕ} (h : ¬ Nat.Coprime d M) :
    diamondLinOne M k d = LinearMap.id :=
  diamondLinOne_of_not fun ⟨_, hγ⟩ => h hγ.coprime

theorem diamondLinOne_one : diamondLinOne M k 1 = LinearMap.id := by
  refine LinearMap.ext fun f => CuspForm.ext fun τ => ?_
  have h1 : IsDiamondLift M 1 1 := ⟨Subgroup.one_mem _, by simp⟩
  rw [diamondLinOne_apply_apply h1, map_one, SlashAction.slash_one, LinearMap.id_apply]

end Diamond

section Hecke

variable (k : ℤ) {M ℓ : ℕ}

def heckeTOne (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (Γ₁ℝ M) k) : CuspForm (Γ₁ℝ M) k :=
  haveI : NeZero M := ⟨fun h => hℓM (h ▸ dvd_zero ℓ)⟩
  { toFun := heckeU k ℓ ⇑f + (⇑(diamondLinOne M k ℓ f)) ∣[k] heckeDiagMatrix ℓ
    slash_action_eq' := fun γ hγ => by
      obtain ⟨σ, hσ⟩ := exists_isDiamondLift_of_coprime (M := M)
        ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)
      rw [coe_diamondLinOne_apply hσ]
      exact Gamma1Hecke.heckeU_add_slash_heckeDiagMatrix_slash k hℓ hℓM
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) σ hσ.1 hσ.2 γ hγ
    holo' := (Gamma1Hecke.mdifferentiable_heckeU (CuspFormClass.holo f) k ℓ).add
      ((CuspFormClass.holo (diamondLinOne M k ℓ f)).slash k _)
    zero_at_cusps' := fun {c} hc =>
      (Gamma1Hecke.isZeroAt_heckeU f hℓ.ne_zero hc).add
        (Gamma1Hecke.isZeroAt_slash_heckeDiagMatrix (diamondLinOne M k ℓ f) hℓ.ne_zero hc) }

@[simp] theorem coe_heckeTOne (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(heckeTOne k hℓ hℓM f) = heckeU k ℓ ⇑f + (⇑(diamondLinOne M k ℓ f)) ∣[k] heckeDiagMatrix ℓ := rfl

def heckeTLinOne (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) : CuspForm (Γ₁ℝ M) k →ₗ[ℂ] CuspForm (Γ₁ℝ M) k where
  toFun := heckeTOne k hℓ hℓM
  map_add' f g := DFunLike.coe_injective <| by
    simp only [coe_heckeTOne, CuspForm.coe_add, map_add, heckeU_add, SlashAction.add_slash]
    abel
  map_smul' c f := DFunLike.coe_injective <| by
    simp only [coe_heckeTOne, CuspForm.IsGLPos.coe_smul, map_smul, heckeU_smul, RingHom.id_apply,
      ModularForm.smul_slash, σ_heckeDiagMatrix, ContinuousAlgEquiv.refl_apply, smul_add]

@[simp] theorem coe_heckeTLinOne_apply (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(heckeTLinOne k hℓ hℓM f) = heckeU k ℓ ⇑f + (⇑(diamondLinOne M k ℓ f)) ∣[k] heckeDiagMatrix ℓ :=
  rfl

theorem coe_heckeTLinOne_apply_of_isDiamondLift (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) {σ : SL(2, ℤ)}
    (hσ : IsDiamondLift M ℓ σ) (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(heckeTLinOne k hℓ hℓM f)
      = heckeU k ℓ ⇑f + (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ)) ∣[k] heckeDiagMatrix ℓ := by
  rw [coe_heckeTLinOne_apply, coe_diamondLinOne_apply hσ]

theorem heckeTLinOne_apply_apply (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (Γ₁ℝ M) k) (τ : ℍ) :
    heckeTLinOne k hℓ hℓM f τ
      = heckeU k ℓ ⇑f τ + ((⇑(diamondLinOne M k ℓ f)) ∣[k] heckeDiagMatrix ℓ) τ :=
  rfl

end Hecke

end CuspForm

end


