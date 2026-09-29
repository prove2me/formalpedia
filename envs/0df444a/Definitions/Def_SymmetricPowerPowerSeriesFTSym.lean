-- Prove2me | Definitions.Def_SymmetricPowerPowerSeriesFTSym
-- name    : SymmetricPowerPowerSeriesFTSym
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/624e5766-e5c8-5599-a3d1-eef3aea6cd6c
-- title:
--   Symmetric power series as power series in elementary symmetric polynomials
-- statement:
--   Fix a commutative ring $k$ and $r \in \mathbb{N}$. The module first records the action of $\mathrm{Perm}(\mathrm{Fin}\ r)$ on $\mathrm{MvPowerSeries}(\mathrm{Fin}\ r)\ k$ by permuting the variables: `permMulSemiringActionMvPowerSeries` gives the `MulSemiringAction` whose scalar action is $\sigma \cdot p =$ `MvPowerSeries.renameEquiv k σ p`, and `permSMulCommClassMvPowerSeries` records that this commutes with the $k$-action.
--
--   The arithmetic core works with the family `es k r i = MvPolynomial.esymm (Fin r) k (i+1)` indexed by $i \in \mathrm{Fin}\ r$, i.e. the elementary symmetric polynomials $e_1,\dots,e_r$, and its image `ea k r` in the power series ring. Since $e_{i+1}$ is homogeneous of degree $i+1$ (`esymm_isHomogeneous`), it has zero constant term, so the family is substitutable (`hasSubst_ea`). The weight of an exponent vector is `wt d = ∑_i (i+1) · d i`, so that the monomial `eP d = ∏_i (es k r i)^{d i}` is homogeneous of degree `wt d` (`eP_isHomogeneous`); `wtSet r N` and `degSet r N` are the finite sets of exponent vectors of weight, respectively total degree, equal to $N$, cut out inside the box $\mathrm{Iic}(\mathrm{bnd}\ N)$ with `bnd N` the constant vector $N$. Coefficientwise formulae (`coeff_aeval_es`, `coeff_subst_ea`, `coeff_subst_ea_eq_coeff_aeval`) express the $e$-coefficient of a substituted series as a finite sum over `wtSet r e.degree`, reducing substitution in each degree to a polynomial truncation; from this come injectivity (`subst_ea_injective`), permutation-invariance of every substituted series (`rename_subst_ea`) and, degree by degree via the fundamental theorem of symmetric polynomials, surjectivity onto invariant series (`exists_subst_ea_eq`).
--
--   The outcome is `substEsymmAlgHom`, the $k$-algebra map sending $f$ to $f(e_1,\dots,e_r)$, viewed as landing in the fixed-point subalgebra, proved bijective in `substEsymmAlgHom_bijective`, and `mvPowerSeriesEsymmAlgEquiv`, the resulting $k$-algebra isomorphism from the subalgebra of permutation-invariant power series to $\mathrm{MvPowerSeries}(\mathrm{Fin}\ r)\ k$; it is the inverse of substitution, and its inverse carries $X_i$ to $e_{i+1}$ (`mvPowerSeriesEsymmAlgEquiv_symm_X`).
--
--   **Relation to Mathlib.** The polynomial input is Mathlib's fundamental theorem of symmetric polynomials, `MvPolynomial.esymmAlgHom_fin_bijective`, together with Mathlib's substitution and renaming API for `MvPowerSeries`; the power series analogue established here, and the permutation action on `MvPowerSeries` by renaming, are the project's own.
--
--   **Where it is used.** The isomorphism is used in the project's work on symmetric powers of algebraic curves, where the invariants of a power series ring under permutation of the variables must be identified with a power series ring in the same number of variables.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_SymmetricPowerPowerSeriesFTSym.lean

import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Algebra.Algebra.Subalgebra.Operations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve.SymmetricPower

universe u

section Action

variable (k : Type u) [CommRing k] (r : ℕ)

@[reducible]
def permMulSemiringActionMvPowerSeries :
    MulSemiringAction (Equiv.Perm (Fin r)) (MvPowerSeries (Fin r) k) where
  smul σ p := MvPowerSeries.renameEquiv k σ p
  one_smul p := by
    show MvPowerSeries.renameEquiv k (1 : Equiv.Perm (Fin r)) p = p
    rw [Equiv.Perm.one_def, MvPowerSeries.renameEquiv_refl]; rfl
  mul_smul σ τ p := by
    show MvPowerSeries.renameEquiv k (σ * τ) p =
      MvPowerSeries.renameEquiv k σ (MvPowerSeries.renameEquiv k τ p)
    have : σ * τ = Equiv.trans τ σ := rfl
    rw [this, ← MvPowerSeries.renameEquiv_trans]
    rfl
  smul_zero σ := map_zero _
  smul_add σ p q := map_add _ p q
  smul_one σ := map_one _
  smul_mul σ p q := map_mul _ p q

@[reducible]
def permSMulCommClassMvPowerSeries :
    letI := permMulSemiringActionMvPowerSeries k r
    SMulCommClass (Equiv.Perm (Fin r)) k (MvPowerSeries (Fin r) k) := by
  letI := permMulSemiringActionMvPowerSeries k r
  refine ⟨fun σ c p => ?_⟩
  show MvPowerSeries.renameEquiv k σ (c • p) = c • MvPowerSeries.renameEquiv k σ p
  exact map_smul _ c p

end Action

namespace PowerSeriesFTSym

variable {k : Type u} [CommRing k] {r : ℕ}

variable (k r) in

def es (i : Fin r) : MvPolynomial (Fin r) k := MvPolynomial.esymm (Fin r) k (i + 1)

variable (k r) in

def ea (i : Fin r) : MvPowerSeries (Fin r) k := (es k r i : MvPowerSeries (Fin r) k)

theorem esymm_isHomogeneous (n : ℕ) : (MvPolynomial.esymm (Fin r) k n).IsHomogeneous n := by
  show MvPolynomial.IsHomogeneous
    (∑ t ∈ Finset.powersetCard n Finset.univ, ∏ i ∈ t, (MvPolynomial.X i : MvPolynomial (Fin r) k)) n
  apply MvPolynomial.IsHomogeneous.sum
  intro t ht
  have h := MvPolynomial.IsHomogeneous.prod t (fun i : Fin r => (MvPolynomial.X i : MvPolynomial (Fin r) k))
    (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X k i)
  rwa [Finset.sum_const, smul_eq_mul, mul_one, (Finset.mem_powersetCard.mp ht).2] at h

theorem constantCoeff_ea (i : Fin r) : MvPowerSeries.constantCoeff (ea k r i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ea, MvPolynomial.coeff_coe]
  exact (esymm_isHomogeneous (i + 1)).coeff_eq_zero (by simp)

variable (k r) in
theorem hasSubst_ea : MvPowerSeries.HasSubst (ea k r) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero constantCoeff_ea

def wt (d : Fin r →₀ ℕ) : ℕ := d.sum fun i n => ((i : ℕ) + 1) * n

theorem le_wt (d : Fin r →₀ ℕ) (i : Fin r) : d i ≤ wt d := by
  by_cases hi : i ∈ d.support
  · calc d i ≤ ((i : ℕ) + 1) * d i := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      _ ≤ wt d := Finset.single_le_sum (f := fun j : Fin r => ((j : ℕ) + 1) * d j) (fun _ _ => Nat.zero_le _) hi
  · rw [Finsupp.notMem_support_iff.mp hi]; exact Nat.zero_le _

def eP (d : Fin r →₀ ℕ) : MvPolynomial (Fin r) k := d.prod fun i n => es k r i ^ n

theorem eP_isHomogeneous (d : Fin r →₀ ℕ) : (eP (k := k) d).IsHomogeneous (wt d) :=
  MvPolynomial.IsHomogeneous.prod d.support (fun i => es k r i ^ d i) (fun i => ((i : ℕ) + 1) * d i)
    fun i _ => (esymm_isHomogeneous (i + 1)).pow (d i)

theorem prod_ea_eq_coe_eP (d : Fin r →₀ ℕ) :
    (d.prod fun s n => ea k r s ^ n) = ((eP d : MvPolynomial (Fin r) k) : MvPowerSeries (Fin r) k) := by
  simp only [Finsupp.prod, eP, ea]
  rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply]

def bnd (N : ℕ) : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N

def wtSet (r : ℕ) (N : ℕ) : Finset (Fin r →₀ ℕ) := (Finset.Iic (bnd N)).filter fun d => wt d = N

theorem mem_wtSet {N : ℕ} {d : Fin r →₀ ℕ} : d ∈ wtSet r N ↔ wt d = N := by
  rw [wtSet, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
  intro h i
  rw [bnd, Finsupp.coe_equivFunOnFinite_symm]
  exact h ▸ le_wt d i

def degSet (r : ℕ) (N : ℕ) : Finset (Fin r →₀ ℕ) := (Finset.Iic (bnd N)).filter fun e => e.degree = N

theorem mem_degSet {N : ℕ} {e : Fin r →₀ ℕ} : e ∈ degSet r N ↔ e.degree = N := by
  rw [degSet, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
  intro h i
  rw [bnd, Finsupp.coe_equivFunOnFinite_symm]
  exact h ▸ Finsupp.le_degree i e

theorem coeff_aeval_es (q : MvPolynomial (Fin r) k) (e : Fin r →₀ ℕ) :
    MvPolynomial.coeff e (MvPolynomial.aeval (es k r) q)
      = ∑ d ∈ wtSet r e.degree, MvPolynomial.coeff d q * MvPolynomial.coeff e (eP (k := k) d) := by
  conv_lhs => rw [q.as_sum, map_sum, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul]
  change ∑ d ∈ q.support, MvPolynomial.coeff d q * MvPolynomial.coeff e (eP (k := k) d) = _
  rw [← Finset.sum_filter_add_sum_filter_not q.support (fun d => wt d = e.degree)]
  have h0 : ∑ d ∈ q.support.filter (fun d => ¬ wt d = e.degree),
      MvPolynomial.coeff d q * MvPolynomial.coeff e (eP (k := k) d) = 0 :=
    Finset.sum_eq_zero fun d hd => by
      rw [(eP_isHomogeneous d).coeff_eq_zero (Ne.symm (Finset.mem_filter.mp hd).2), mul_zero]
  rw [h0, add_zero]
  have hset : q.support.filter (fun d => wt d = e.degree) = (wtSet r e.degree).filter (· ∈ q.support) := by
    ext d
    simp only [Finset.mem_filter, mem_wtSet]
    exact and_comm
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, zero_mul]

theorem coeff_subst_ea (f : MvPowerSeries (Fin r) k) (e : Fin r →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst (ea k r) f)
      = ∑ d ∈ wtSet r e.degree, MvPowerSeries.coeff d f * MvPolynomial.coeff e (eP (k := k) d) := by
  rw [MvPowerSeries.coeff_subst (hasSubst_ea k r)]
  rw [finsum_eq_sum_of_support_subset _ (s := wtSet r e.degree) ?_]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [prod_ea_eq_coe_eP, MvPolynomial.coeff_coe, smul_eq_mul]
  · intro d hd
    rw [Function.mem_support, prod_ea_eq_coe_eP, MvPolynomial.coeff_coe] at hd
    rw [Finset.mem_coe, mem_wtSet]
    by_contra hne
    exact hd (by rw [(eP_isHomogeneous d).coeff_eq_zero (Ne.symm hne), smul_zero])

theorem aeval_truncFinset_isHomogeneous (f : MvPowerSeries (Fin r) k) (N : ℕ) :
    (MvPolynomial.aeval (es k r) (MvPowerSeries.truncFinset k (wtSet r N) f)).IsHomogeneous N := by
  rw [MvPowerSeries.truncFinset_apply, map_sum]
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, ← mem_wtSet.mp hd]
  exact (eP_isHomogeneous d).C_mul _

theorem coeff_subst_ea_eq_coeff_aeval (f : MvPowerSeries (Fin r) k) (e : Fin r →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst (ea k r) f)
      = MvPolynomial.coeff e
          (MvPolynomial.aeval (es k r) (MvPowerSeries.truncFinset k (wtSet r e.degree) f)) := by
  rw [coeff_subst_ea, coeff_aeval_es]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [MvPowerSeries.coeff_truncFinset_of_mem _ hd]

theorem aeval_es_injective : Function.Injective (MvPolynomial.aeval (R := k) (es k r)) := by
  intro p q h
  apply (MvPolynomial.esymmAlgHom_fin_bijective (R := k) r).1
  apply Subtype.ext
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.esymmAlgHom_apply]
  exact h

theorem subst_ea_injective : Function.Injective (MvPowerSeries.subst (R := k) (ea k r)) := by
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_ea k r)]
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  rw [MvPowerSeries.coe_substAlgHom] at hf
  ext d

  have hP : MvPolynomial.aeval (es k r) (MvPowerSeries.truncFinset k (wtSet r (wt d)) f) = 0 := by
    ext e
    by_cases he : e.degree = wt d
    · rw [← he, ← coeff_subst_ea_eq_coeff_aeval, hf, map_zero, MvPolynomial.coeff_zero]
    · rw [(aeval_truncFinset_isHomogeneous f (wt d)).coeff_eq_zero he, MvPolynomial.coeff_zero]
  have h0 : MvPowerSeries.truncFinset k (wtSet r (wt d)) f = 0 :=
    aeval_es_injective (by rw [hP, map_zero])
  have := congrArg (MvPolynomial.coeff d) h0
  rwa [MvPowerSeries.coeff_truncFinset_of_mem _ (mem_wtSet.mpr rfl), MvPolynomial.coeff_zero] at this

theorem rename_subst_ea (σ : Equiv.Perm (Fin r)) (f : MvPowerSeries (Fin r) k) :
    MvPowerSeries.rename σ (MvPowerSeries.subst (ea k r) f) = MvPowerSeries.subst (ea k r) f := by
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_ea k r) (MvPowerSeries.HasSubst.X_comp _)]
  congr 1
  funext i
  rw [← MvPowerSeries.rename_eq_subst, ea, MvPowerSeries.rename_coe, es, MvPolynomial.rename_esymm]

theorem coeff_mapDomain_of_fixed {g : MvPowerSeries (Fin r) k}
    (hg : ∀ σ : Equiv.Perm (Fin r), MvPowerSeries.rename σ g = g) (τ : Equiv.Perm (Fin r))
    (x : Fin r →₀ ℕ) : MvPowerSeries.coeff (Finsupp.mapDomain τ x) g = MvPowerSeries.coeff x g := by
  conv_lhs => rw [← hg τ]
  have h : Finsupp.embDomain τ.toEmbedding x = Finsupp.mapDomain τ x := Finsupp.embDomain_eq_mapDomain _ _
  rw [← h]
  exact MvPowerSeries.coeff_embDomain_rename τ.toEmbedding g x

theorem truncFinset_degSet_isSymmetric {g : MvPowerSeries (Fin r) k}
    (hg : ∀ σ : Equiv.Perm (Fin r), MvPowerSeries.rename σ g = g) (N : ℕ) :
    (MvPowerSeries.truncFinset k (degSet r N) g).IsSymmetric := by
  intro σ
  ext e
  have he : e = Finsupp.mapDomain σ (Finsupp.mapDomain σ.symm e) := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  rw [he, MvPolynomial.coeff_rename_mapDomain σ σ.injective, ← he]
  by_cases hN : e ∈ degSet r N
  · have hN' : Finsupp.mapDomain σ.symm e ∈ degSet r N := by
      rw [mem_degSet] at hN ⊢; rw [Finsupp.degree_mapDomain]; exact hN
    rw [MvPowerSeries.coeff_truncFinset_of_mem _ hN, MvPowerSeries.coeff_truncFinset_of_mem _ hN',
      coeff_mapDomain_of_fixed hg]
  · have hN' : Finsupp.mapDomain σ.symm e ∉ degSet r N := by
      rw [mem_degSet] at hN ⊢; rw [Finsupp.degree_mapDomain]; exact hN
    rw [MvPowerSeries.coeff_truncFinset_eq_zero _ hN, MvPowerSeries.coeff_truncFinset_eq_zero _ hN']

theorem exists_aeval_eq_truncFinset {g : MvPowerSeries (Fin r) k}
    (hg : ∀ σ : Equiv.Perm (Fin r), MvPowerSeries.rename σ g = g) (N : ℕ) :
    ∃ q : MvPolynomial (Fin r) k,
      MvPolynomial.aeval (es k r) q = MvPowerSeries.truncFinset k (degSet r N) g := by
  obtain ⟨q, hq⟩ := (MvPolynomial.esymmAlgHom_fin_bijective (R := k) r).2
    ⟨_, truncFinset_degSet_isSymmetric hg N⟩
  refine ⟨q, ?_⟩
  have := congrArg Subtype.val hq
  rwa [MvPolynomial.esymmAlgHom_apply] at this

theorem exists_subst_ea_eq {g : MvPowerSeries (Fin r) k}
    (hg : ∀ σ : Equiv.Perm (Fin r), MvPowerSeries.rename σ g = g) :
    ∃ f : MvPowerSeries (Fin r) k, MvPowerSeries.subst (ea k r) f = g := by
  choose q hq using exists_aeval_eq_truncFinset hg
  refine ⟨fun d => MvPolynomial.coeff d (q (wt d)), ?_⟩
  ext e
  rw [coeff_subst_ea]
  calc ∑ d ∈ wtSet r e.degree, MvPowerSeries.coeff d (fun d => MvPolynomial.coeff d (q (wt d)))
          * MvPolynomial.coeff e (eP (k := k) d)
        = ∑ d ∈ wtSet r e.degree, MvPolynomial.coeff d (q e.degree) * MvPolynomial.coeff e (eP (k := k) d) :=
          Finset.sum_congr rfl fun d hd => by
            rw [show MvPowerSeries.coeff d (fun d => MvPolynomial.coeff d (q (wt d)))
              = MvPolynomial.coeff d (q (wt d)) from rfl, mem_wtSet.mp hd]
    _ = MvPolynomial.coeff e (MvPolynomial.aeval (es k r) (q e.degree)) := (coeff_aeval_es _ _).symm
    _ = MvPowerSeries.coeff e g := by
          rw [hq, MvPowerSeries.coeff_truncFinset_of_mem _ (mem_degSet.mpr rfl)]

end PowerSeriesFTSym

section Equiv

open PowerSeriesFTSym

variable (k : Type u) [CommRing k] (r : ℕ)

def substEsymmAlgHom :
    letI := permMulSemiringActionMvPowerSeries k r
    letI := permSMulCommClassMvPowerSeries k r
    MvPowerSeries (Fin r) k →ₐ[k]
      FixedPoints.subalgebra k (MvPowerSeries (Fin r) k) (Equiv.Perm (Fin r)) :=
  letI := permMulSemiringActionMvPowerSeries k r
  letI := permSMulCommClassMvPowerSeries k r
  (MvPowerSeries.substAlgHom (hasSubst_ea k r)).codRestrict
    (FixedPoints.subalgebra k (MvPowerSeries (Fin r) k) (Equiv.Perm (Fin r))) fun f σ => by
      change MvPowerSeries.renameEquiv k σ (MvPowerSeries.substAlgHom (hasSubst_ea k r) f) = _
      rw [MvPowerSeries.coe_substAlgHom]
      exact rename_subst_ea σ f

theorem substEsymmAlgHom_apply_coe (f : MvPowerSeries (Fin r) k) :
    ((substEsymmAlgHom k r f : _) : MvPowerSeries (Fin r) k) = MvPowerSeries.subst (ea k r) f := by
  change MvPowerSeries.substAlgHom (hasSubst_ea k r) f = _
  rw [MvPowerSeries.coe_substAlgHom]

theorem substEsymmAlgHom_bijective : Function.Bijective (substEsymmAlgHom k r) := by
  letI := permMulSemiringActionMvPowerSeries k r
  letI := permSMulCommClassMvPowerSeries k r
  constructor
  · intro f g h
    apply subst_ea_injective
    rw [← substEsymmAlgHom_apply_coe, ← substEsymmAlgHom_apply_coe, h]
  · rintro ⟨g, hg⟩
    obtain ⟨f, hf⟩ := exists_subst_ea_eq (g := g) fun σ => hg σ
    exact ⟨f, Subtype.ext (by rw [substEsymmAlgHom_apply_coe, hf])⟩

def mvPowerSeriesEsymmAlgEquiv :
    letI := permMulSemiringActionMvPowerSeries k r
    letI := permSMulCommClassMvPowerSeries k r
    (FixedPoints.subalgebra k (MvPowerSeries (Fin r) k) (Equiv.Perm (Fin r)))
      ≃ₐ[k] MvPowerSeries (Fin r) k :=
  letI := permMulSemiringActionMvPowerSeries k r
  letI := permSMulCommClassMvPowerSeries k r
  (AlgEquiv.ofBijective (substEsymmAlgHom k r) (substEsymmAlgHom_bijective k r)).symm

theorem mvPowerSeriesEsymmAlgEquiv_symm_apply_coe (f : MvPowerSeries (Fin r) k) :
    (((mvPowerSeriesEsymmAlgEquiv k r).symm f : _) : MvPowerSeries (Fin r) k)
      = MvPowerSeries.subst (ea k r) f := by
  rw [mvPowerSeriesEsymmAlgEquiv, AlgEquiv.symm_symm]
  exact substEsymmAlgHom_apply_coe k r f

theorem mvPowerSeriesEsymmAlgEquiv_symm_X (i : Fin r) :
    (((mvPowerSeriesEsymmAlgEquiv k r).symm (MvPowerSeries.X i) : _) : MvPowerSeries (Fin r) k)
      = (MvPolynomial.esymm (Fin r) k (i + 1) : MvPowerSeries (Fin r) k) := by
  rw [mvPowerSeriesEsymmAlgEquiv_symm_apply_coe, MvPowerSeries.subst_X (hasSubst_ea k r)]
  rfl

end Equiv

end AlgebraicCurve.SymmetricPower

end

#print axioms AlgebraicCurve.SymmetricPower.mvPowerSeriesEsymmAlgEquiv
#print axioms AlgebraicCurve.SymmetricPower.mvPowerSeriesEsymmAlgEquiv_symm_X


