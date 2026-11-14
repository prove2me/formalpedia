-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBLie
-- name    : RPLib_S4_AlgGrpBLie
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:36:50.894454+00:00
-- url     : https://prove2.me/theorems/5b07aca6-fc17-402a-8b24-e47e0a04fb7d
-- title:
--   Larsen's alternative library: the Lie algebra of a subset of `GL_n(K)`)
-- statement:
--   For `Z ⊆ GL_n(K)` (any field `K`), `lieS Z ⊆ gl_n(K)` is the tangent space at `1` of the Zariski
--   closure of `Z`: the matrices `X` such that every polynomial in the coordinates `(g, g⁻¹)` vanishing
--   on `Z` has zero derivative at `1` in the direction `(X, -X)`. Equivalently (`mem_lieS_iff_dual`,
--   when `1 ∈ Z`), the `K[ε]`-point `1 + ε X` lies on every such polynomial (`K[ε]`-points).
--
--   Main results: `lieS Z` is a `K`-subspace, monotone in `Z`, unchanged by Zariski closure; polynomial
--   maps carry tangent vectors (`lieS_subst`); if `g Z g⁻¹ ⊆ Z` then `Ad(g)` preserves `lieS Z`
--   (`conj_mem_lieS`), so `lieS (G ∩ SL)` is `Ad(G)`-stable (`conj_mem_lieS_inf_sl`); if `Z ⊆ SL` then
--   `lieS Z ⊆ sl` (`trace_eq_zero_of_mem_lieS`).
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpAIdComp

/-!
# S4-AlgGrpB, file Lie: the Lie algebra of a subset of `GL_n(K)` (spike API (A2))

For `Z ⊆ GL_n(K)` (any field `K`), `lieS Z ⊆ gl_n(K)` is the tangent space at `1` of the Zariski
closure of `Z`: the matrices `X` such that every polynomial in the coordinates `(g, g⁻¹)` vanishing
on `Z` has zero derivative at `1` in the direction `(X, -X)`. Equivalently (`mem_lieS_iff_dual`,
when `1 ∈ Z`), the `K[ε]`-point `1 + ε X` lies on every such polynomial (`K[ε]`-points).

Main results: `lieS Z` is a `K`-subspace, monotone in `Z`, unchanged by Zariski closure; polynomial
maps carry tangent vectors (`lieS_subst`); if `g Z g⁻¹ ⊆ Z` then `Ad(g)` preserves `lieS Z`
(`conj_mem_lieS`), so `lieS (G ∩ SL)` is `Ad(G)`-stable (`conj_mem_lieS_inf_sl`); if `Z ⊆ SL` then
`lieS Z ⊆ sl` (`trace_eq_zero_of_mem_lieS`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

section Deriv

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type*} [Field K]

/-- The derivative at `c` in direction `w` of a polynomial `f`. -/
def dirDeriv (c w : σ → K) (f : MvPolynomial σ K) : K :=
  ∑ v, eval c (pderiv v f) * w v

/-- The `K[ε]`-point `c + ε w`. -/
def dpt (c w : σ → K) : σ → DualNumber K :=
  fun v => TrivSqZeroExt.inl (c v) + TrivSqZeroExt.inr (w v)

theorem fst_aeval_dpt (c w : σ → K) (f : MvPolynomial σ K) :
    TrivSqZeroExt.fst (aeval (dpt c w) f) = eval c f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp, dpt]

theorem snd_aeval_dpt (c w : σ → K) (f : MvPolynomial σ K) :
    TrivSqZeroExt.snd (aeval (dpt c w) f) = dirDeriv c w f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [dirDeriv, TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq => simp [hp, hq, dirDeriv, add_mul, Finset.sum_add_distrib]
  | mul_X p v hp =>
    rw [map_mul, DualNumber.snd_mul, hp, fst_aeval_dpt]
    have key : ∀ u, eval c (pderiv u (p * X v)) * w u =
        (if u = v then eval c p * w v else 0) + c v * (eval c (pderiv u p) * w u) := by
      intro u
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : u = v
      · subst h
        simp
        ring
      · simp [Ne.symm h, h]
        ring
    simp only [dirDeriv, key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      ← Finset.mul_sum]
    simp [dpt]
    ring

theorem dirDeriv_add_right (c w w' : σ → K) (f : MvPolynomial σ K) :
    dirDeriv c (w + w') f = dirDeriv c w f + dirDeriv c w' f := by
  simp [dirDeriv, mul_add, Finset.sum_add_distrib]

theorem dirDeriv_smul_right (c w : σ → K) (a : K) (f : MvPolynomial σ K) :
    dirDeriv c (a • w) f = a * dirDeriv c w f := by
  simp only [dirDeriv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dirDeriv_zero_right (c : σ → K) (f : MvPolynomial σ K) : dirDeriv c 0 f = 0 := by
  simp [dirDeriv]

end Deriv

section GLn

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The tangent direction of `1 + ε X` in the coordinates `(g, g⁻¹)`: `(X, -X)`. -/
def dvec (X : Matrix n n K) : Var n → K :=
  Sum.elim (fun ij => X ij.1 ij.2) (fun ij => -X ij.1 ij.2)

@[simp] theorem dvec_inl (X : Matrix n n K) (ij : n × n) : dvec X (Sum.inl ij) = X ij.1 ij.2 := rfl

@[simp] theorem dvec_inr (X : Matrix n n K) (ij : n × n) : dvec X (Sum.inr ij) = -X ij.1 ij.2 :=
  rfl

theorem dvec_add (X Y : Matrix n n K) : dvec (X + Y) = dvec X + dvec Y := by
  funext v; rcases v with ij | ij <;> simp [add_comm]

theorem dvec_smul (a : K) (X : Matrix n n K) : dvec (a • X) = a • dvec X := by
  funext v; rcases v with ij | ij <;> simp

theorem dvec_zero : dvec (0 : Matrix n n K) = 0 := by
  funext v; rcases v with ij | ij <;> simp

/-- The Lie algebra (tangent space at `1`) of a subset `Z ⊆ GL_n(K)`. -/
def lieS (Z : Set (Matrix.GeneralLinearGroup n K)) : Submodule K (Matrix n n K) where
  carrier := {X | ∀ f ∈ vanI Z, dirDeriv (crd 1) (dvec X) f = 0}
  add_mem' := by
    intro X Y hX hY f hf
    rw [dvec_add, dirDeriv_add_right, hX f hf, hY f hf, add_zero]
  zero_mem' := by
    intro f _
    rw [dvec_zero, dirDeriv_zero_right]
  smul_mem' := by
    intro a X hX f hf
    rw [dvec_smul, dirDeriv_smul_right, hX f hf, mul_zero]

theorem mem_lieS {Z : Set (Matrix.GeneralLinearGroup n K)} {X : Matrix n n K} :
    X ∈ lieS Z ↔ ∀ f ∈ vanI Z, dirDeriv (crd 1) (dvec X) f = 0 := Iff.rfl

/-- The `K[ε]`-point `1 + ε X` of `GL_n` (its inverse is `1 - ε X`). -/
def ptD (X : Matrix n n K) : Var n → DualNumber K := dpt (crd 1) (dvec X)

theorem snd_aeval_ptD (X : Matrix n n K) (f : MvPolynomial (Var n) K) :
    TrivSqZeroExt.snd (aeval (ptD X) f) = dirDeriv (crd 1) (dvec X) f :=
  snd_aeval_dpt _ _ f

/-- `K[ε]`-points: `X ∈ Lie Z` iff `1 + ε X` satisfies every equation of `Z`. -/
theorem mem_lieS_iff_dual {Z : Set (Matrix.GeneralLinearGroup n K)} (h1 : (1 : _) ∈ Z)
    (X : Matrix n n K) : X ∈ lieS Z ↔ ∀ f ∈ vanI Z, aeval (ptD X) f = 0 := by
  constructor
  · intro hX f hf
    ext
    · rw [ptD, fst_aeval_dpt]
      exact mem_vanI.1 hf 1 h1
    · rw [snd_aeval_ptD]
      exact hX f hf
  · intro h f hf
    rw [← snd_aeval_ptD, h f hf]
    rfl

theorem vanI_anti {Z Z' : Set (Matrix.GeneralLinearGroup n K)} (h : Z ⊆ Z') :
    vanI Z' ≤ vanI Z := fun _ hf => mem_vanI.2 fun g hg => mem_vanI.1 hf g (h hg)

theorem lieS_mono {Z Z' : Set (Matrix.GeneralLinearGroup n K)} (h : Z ⊆ Z') :
    lieS Z ≤ lieS Z' := fun _ hX f hf => hX f (vanI_anti h hf)

attribute [local instance] zarTop in
theorem vanI_closure (Z : Set (Matrix.GeneralLinearGroup n K)) : vanI (closure Z) = vanI Z := by
  refine le_antisymm (vanI_anti subset_closure) fun f hf => mem_vanI.2 fun g hg => ?_
  rw [closure_eq_zeroS_vanI] at hg
  exact hg f hf

attribute [local instance] zarTop in
/-- The Lie algebra only depends on the Zariski closure. -/
theorem lieS_closure (Z : Set (Matrix.GeneralLinearGroup n K)) : lieS (closure Z) = lieS Z := by
  ext X
  simp only [mem_lieS, vanI_closure]

theorem eval_bind₁' {m : Type*} (c : Var n → K) (q : m → MvPolynomial (Var n) K)
    (f : MvPolynomial m K) : eval c (bind₁ q f) = eval (fun v => eval c (q v)) f := by
  change eval₂Hom (RingHom.id K) c (bind₁ q f) = _
  rw [eval₂Hom_bind₁]
  rfl

/-- Polynomial maps carry tangent vectors: if the substitution `q` maps `Z` into `Z'` and sends
`1 + ε X` to `1 + ε Y`, then `X ∈ Lie Z` implies `Y ∈ Lie Z'`. -/
theorem lieS_subst {m : Type*} [Fintype m] [DecidableEq m] {Z : Set (Matrix.GeneralLinearGroup n K)}
    {Z' : Set (Matrix.GeneralLinearGroup m K)} (q : Var m → MvPolynomial (Var n) K)
    (hq : ∀ g ∈ Z, ∃ g' ∈ Z', ∀ v, eval (crd g) (q v) = crd g' v)
    {X : Matrix n n K} {Y : Matrix m m K} (hXY : ∀ v, aeval (ptD X) (q v) = ptD Y v)
    (hX : X ∈ lieS Z) : Y ∈ lieS Z' := by
  intro f hf
  have hb : bind₁ q f ∈ vanI Z := by
    refine mem_vanI.2 fun g hg => ?_
    obtain ⟨g', hg', hgg'⟩ := hq g hg
    rw [eval_bind₁']
    have : (fun v => eval (crd g) (q v)) = crd g' := funext hgg'
    rw [this]
    exact mem_vanI.1 hf g' hg'
  have h2 := hX _ hb
  rw [← snd_aeval_ptD, aeval_bind₁] at h2
  rw [← snd_aeval_ptD]
  have : (fun v => aeval (ptD X) (q v)) = ptD Y := funext hXY
  rwa [this] at h2

/-- Polynomials giving the coordinates of `g h g⁻¹` in terms of those of `h`. -/
def conjPoly (g : Matrix.GeneralLinearGroup n K) : Var n → MvPolynomial (Var n) K :=
  Sum.elim
    (fun ij => ∑ l, ∑ k, C ((g : Matrix n n K) ij.1 k *
      ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) l ij.2) * X (Sum.inl (k, l)))
    (fun ij => ∑ l, ∑ k, C ((g : Matrix n n K) ij.1 k *
      ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) l ij.2) * X (Sum.inr (k, l)))

theorem sum_conj {R : Type*} [CommRing R] (A B M : Matrix n n R) (i j : n) :
    ∑ l, ∑ k, A i k * B l j * M k l = (A * M * B) i j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem eval_conjPoly (g h : Matrix.GeneralLinearGroup n K) (v : Var n) :
    eval (crd h) (conjPoly g v) = crd (g * h * g⁻¹) v := by
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [conjPoly, Sum.elim_inl, map_sum, map_mul, eval_C, eval_X, crd_inl]
    rw [sum_conj]
    simp [Units.val_mul]
  · simp only [conjPoly, Sum.elim_inr, map_sum, map_mul, eval_C, eval_X, crd_inr]
    rw [sum_conj]
    simp [Units.val_mul, mul_inv_rev, mul_assoc]

theorem aeval_C_mul_X (pt : Var n → DualNumber K) (c : K) (w : Var n) :
    aeval pt (C c * X w : MvPolynomial (Var n) K) = c • pt w := by
  rw [map_mul, aeval_C, aeval_X, Algebra.smul_def]

theorem aeval_ptD_conjPoly (g : Matrix.GeneralLinearGroup n K) (X : Matrix n n K) (v : Var n) :
    aeval (ptD X) (conjPoly g v) =
      ptD ((g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) v := by
  have hgg : (g : Matrix n n K) * 1 * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) = 1 := by
    rw [Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rcases v with ⟨i, j⟩ | ⟨i, j⟩
  · ext
    · simp only [conjPoly, Sum.elim_inl, map_sum, aeval_C_mul_X, TrivSqZeroExt.fst_sum,
        TrivSqZeroExt.fst_smul, smul_eq_mul, ptD, dpt, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, crd_inl, Units.val_one]
      rw [sum_conj, hgg]
    · simp only [conjPoly, Sum.elim_inl, map_sum, aeval_C_mul_X, TrivSqZeroExt.snd_sum,
        TrivSqZeroExt.snd_smul, smul_eq_mul, ptD, dpt, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, dvec_inl]
      rw [sum_conj]
  · ext
    · simp only [conjPoly, Sum.elim_inr, map_sum, aeval_C_mul_X, TrivSqZeroExt.fst_sum,
        TrivSqZeroExt.fst_smul, smul_eq_mul, ptD, dpt, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, crd_inr, inv_one, Units.val_one]
      rw [sum_conj, hgg]
    · simp only [conjPoly, Sum.elim_inr, map_sum, aeval_C_mul_X, TrivSqZeroExt.snd_sum,
        TrivSqZeroExt.snd_smul, smul_eq_mul, ptD, dpt, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, dvec_inr]
      have := sum_conj (g : Matrix n n K) ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)
        (-X) i j
      simp only [Matrix.neg_apply, Matrix.mul_neg, Matrix.neg_mul] at this
      rw [this]

/-- If `g` normalises `Z` then `Ad(g)` preserves `Lie Z`. -/
theorem conj_mem_lieS {Z : Set (Matrix.GeneralLinearGroup n K)} {g : Matrix.GeneralLinearGroup n K}
    (hg : ∀ h ∈ Z, g * h * g⁻¹ ∈ Z) {X : Matrix n n K} (hX : X ∈ lieS Z) :
    (g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ∈ lieS Z :=
  lieS_subst (conjPoly g) (fun h hh => ⟨_, hg h hh, eval_conjPoly g h⟩) (aeval_ptD_conjPoly g X) hX

/-- The elements of determinant one. -/
def slSet : Set (Matrix.GeneralLinearGroup n K) := {g | Matrix.det (g : Matrix n n K) = 1}

/-- `Lie (G ∩ SL)` is `Ad(G)`-stable. -/
theorem conj_mem_lieS_inf_sl (G : Subgroup (Matrix.GeneralLinearGroup n K))
    {g : Matrix.GeneralLinearGroup n K} (hg : g ∈ G) {X : Matrix n n K}
    (hX : X ∈ lieS ((G : Set (Matrix.GeneralLinearGroup n K)) ∩ slSet)) :
    (g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ∈
      lieS ((G : Set (Matrix.GeneralLinearGroup n K)) ∩ slSet) := by
  refine conj_mem_lieS (Z := (G : Set (Matrix.GeneralLinearGroup n K)) ∩ slSet)
    (fun h hh => ⟨G.mul_mem (G.mul_mem hg hh.1) (G.inv_mem hg), ?_⟩) hX
  have h2 : Matrix.det (h : Matrix n n K) = 1 := hh.2
  change Matrix.det ((g * h * g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) = 1
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, h2, mul_one, ← Matrix.det_mul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

/-- The generic matrix `(x_{ij})` of the coordinates of `g`. -/
def mX : Matrix n n (MvPolynomial (Var n) K) := Matrix.of fun i j => X (Sum.inl (i, j))

/-- `det (x_{ij})` as a polynomial in the coordinates. -/
def detPoly : MvPolynomial (Var n) K := Matrix.det (mX (n := n) (K := K))

theorem eval_detPoly (g : Matrix.GeneralLinearGroup n K) :
    eval (crd g) (detPoly (n := n)) = Matrix.det (g : Matrix n n K) := by
  rw [detPoly, RingHom.map_det]
  congr 1
  ext i j
  simp [mX]

theorem ptD_mat (X : Matrix n n K) :
    (Matrix.of fun i j => ptD X (Sum.inl (i, j))) =
      1 + (DualNumber.eps : DualNumber K) • X.map (TrivSqZeroExt.inl (M := K)) := by
  ext i j
  · simp [ptD, dpt, Matrix.one_apply, apply_ite TrivSqZeroExt.fst]
  · simp [ptD, dpt, Matrix.one_apply, apply_ite TrivSqZeroExt.snd]

theorem snd_aeval_ptD_detPoly (X : Matrix n n K) :
    TrivSqZeroExt.snd (aeval (ptD X) (detPoly (n := n) (K := K))) = Matrix.trace X := by
  rw [detPoly, AlgHom.map_det]
  have hM : (aeval (ptD X)).mapMatrix (mX (n := n) (K := K)) =
      1 + (DualNumber.eps : DualNumber K) • X.map (TrivSqZeroExt.inl (M := K)) := by
    rw [← ptD_mat]
    refine Matrix.ext fun i j => ?_
    simp [mX]
  rw [hM, Matrix.det_one_add_smul, DualNumber.eps_pow_two, mul_zero, add_zero]
  simp [Matrix.trace, TrivSqZeroExt.fst_sum]

/-- `(A2)`: if `Z ⊆ SL` then `Lie Z ⊆ sl`. -/
theorem trace_eq_zero_of_mem_lieS {Z : Set (Matrix.GeneralLinearGroup n K)} (hZ : Z ⊆ slSet)
    {X : Matrix n n K} (hX : X ∈ lieS Z) : Matrix.trace X = 0 := by
  have hf : detPoly - 1 ∈ vanI Z :=
    mem_vanI.2 fun g hg => by rw [map_sub, eval_detPoly, map_one, hZ hg, sub_self]
  have := hX _ hf
  rw [← snd_aeval_ptD, map_sub, TrivSqZeroExt.snd_sub, snd_aeval_ptD_detPoly, map_one,
    TrivSqZeroExt.snd_one, sub_zero] at this
  exact this

end GLn

end RamanujanPetersson.AlgGrpB

end


