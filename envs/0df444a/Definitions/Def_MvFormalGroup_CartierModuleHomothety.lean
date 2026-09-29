-- Prove2me | Definitions.Def_MvFormalGroup_CartierModuleHomothety
-- name    : MvFormalGroup_CartierModuleHomothety
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/aa5734d6-51db-5142-997d-2b4c0f2506ba
-- title:
--   Teichmüller families and homothety operators on Cartier modules
-- statement:
--   Fix a prime $p$ and a commutative ring $R$. For $a\in R$, `teichFam p a` is the family of multivariate power series in the variables $X_n$, $n\in\mathbb N$, given by $n\mapsto a^{p^n}X_n$; equivalently, it is the pointwise scalar multiple of the family of variables by $(a^{p^n})_n$. Every member has zero constant coefficient, so substitution into the family is admissible, and the resulting substitution operator is Mathlib's rescaling $\mathrm{rescale}(n\mapsto a^{p^n})$. The associated family indexed by $\mathrm{Fin}\,2\times\mathbb N$ produced by `pairFam` is $(i,m)\mapsto a^{p^m}X_{(i,m)}$, and `isEndo_teichFam` asserts `IsEndo p (teichFam p a)`, whose components are substitutability, vanishing of constant coefficients, and a commutation relation with the family `addFam p R`; the verification rests on the fact that a monomial occurring in `addFam p R n` has weight $p^n$ when $X_{(i,m)}$ is given weight $p^m$. Further identities record $\mathrm{teichFam}\,p\,1=X$, $\mathrm{teichFam}\,p\,0=0$, the multiplicativity $\mathrm{subst}(\mathrm{teichFam}\,p\,a)(\mathrm{teichFam}\,p\,b\,n)=\mathrm{teichFam}\,p\,(ab)\,n$, and exchange relations with `frobFam`, `verFam` and `curveFam` (the last giving `PowerSeries.rescale a`).
--
--   For a commutative law $\Phi$ of dimension $d$ over $R$ and $a\in R$, `homothety a` is the additive endomorphism of `CartierModule p Φ` obtained by precomposition with this endomorphism datum: on the underlying $d$-tuples of power series it substitutes $a^{p^n}$ for $X_n$, i.e. applies $\mathrm{rescale}(n\mapsto a^{p^n})$ coordinatewise, so the coefficient at $e$ is multiplied by $\prod_n (a^{p^n})^{e(n)}$. The accompanying results give $\langle 1\rangle=\mathrm{id}$, $\langle 0\rangle f=0$, $\langle ab\rangle=\langle a\rangle\langle b\rangle$ and hence commutativity of the operators; the semilinearity relations $\langle a\rangle V=V\langle a^p\rangle$ (over a base of characteristic $p$) and $F\langle a\rangle=\langle a^p\rangle F$; compatibility with multiplication by natural numbers, with `map` along a homomorphism $\Phi\to\Phi'$ and with `endAct`; the effect on tangent vectors, $\mathrm{tangent}(\langle a\rangle f)=a\cdot\mathrm{tangent}(f)$, and on curves, $\mathrm{curve}(\langle a\rangle f)_j=\mathrm{PowerSeries.rescale}\,a\,(\mathrm{curve}(f)_j)$; and, for the additive law, $\langle a\rangle(\mathrm{addLinear}\,p\,v)=\mathrm{addLinear}\,p\,(a\cdot v)$.
--
--   **Relation to Mathlib.** Mathlib has no multivariate formal group laws or Cartier modules; those notions are the project's own. Substitution of the Teichmüller family is identified with Mathlib's `rescale` on `MvPowerSeries`, and its effect on curves with `PowerSeries.rescale`.
--
--   **Where it is used.** Together with Verschiebung and Frobenius, the operators $\langle a\rangle$ are the third family of operators on the Cartier module of a commutative formal group law, and the relations established here are those of the Cartier ring $\mathrm{Cart}_p(R)$, so that Cartier modules may be treated as modules over it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_CartierModuleHomothety.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R]

def teichFam (a : R) : ℕ → MvPowerSeries ℕ R := fun n => (a ^ p ^ n) • X n

variable {p}

omit hp in
@[simp] theorem teichFam_apply (a : R) (n : ℕ) : teichFam p a n = (a ^ p ^ n) • X n := rfl

omit hp in
theorem teichFam_eq_smul_X (a : R) :
    teichFam p a = (fun n => a ^ p ^ n) • (X : ℕ → MvPowerSeries ℕ R) := rfl

omit hp in
theorem constantCoeff_teichFam (a : R) (n : ℕ) : (teichFam p a n).constantCoeff = 0 := by
  rw [teichFam_apply, smul_eq_C_mul, map_mul, constantCoeff_X, mul_zero]

omit hp in
theorem hasSubst_teichFam (a : R) : HasSubst (teichFam p a) := HasSubst.smul_X _

omit hp in

theorem subst_teichFam (a : R) (f : MvPowerSeries ℕ R) :
    subst (teichFam p a) f = rescale (fun n => a ^ p ^ n) f :=
  (rescale_eq_subst _ f).symm

omit hp in

theorem pairFam_teichFam (a : R) :
    pairFam (teichFam p a) = (fun im : Fin 2 × ℕ => a ^ p ^ im.2) • X := by
  funext ⟨i, m⟩
  rw [pairFam_apply, teichFam_apply, subst_smul (hasSubst_blk i), subst_X (hasSubst_blk i)]
  rfl

theorem isEndo_teichFam (a : R) : IsEndo p (teichFam p a) := by
  refine ⟨hasSubst_teichFam a, constantCoeff_teichFam a, fun n => ?_⟩
  rw [teichFam_apply, subst_smul (hasSubst_addFam p R), subst_X (hasSubst_addFam p R),
    pairFam_teichFam, ← rescale_eq_subst]
  ext e
  rw [coeff_smul, coeff_rescale]
  by_cases he : coeff e (addFam p R n) = 0
  · rw [he, mul_zero, mul_zero]
  · congr 1
    rw [← weight_eq_of_coeff_addFam_ne_zero p R he, Finsupp.weight_apply, Finsupp.prod,
      Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun im _ => ?_
    rw [← pow_mul, weight_apply, one_mul, smul_eq_mul, mul_comm]

omit hp in

theorem teichFam_one : teichFam p (1 : R) = X := by
  funext n
  rw [teichFam_apply, one_pow, one_smul]

theorem teichFam_zero : teichFam p (0 : R) = 0 := by
  funext n
  rw [teichFam_apply, zero_pow (pow_ne_zero n hp.out.ne_zero), zero_smul, Pi.zero_apply]

omit hp in

theorem subst_teichFam_teichFam (a b : R) (n : ℕ) :
    subst (teichFam p a) (teichFam p b n) = teichFam p (a * b) n := by
  rw [teichFam_apply, subst_smul (hasSubst_teichFam a), subst_X (hasSubst_teichFam a),
    teichFam_apply, teichFam_apply, smul_smul, mul_pow, mul_comm]

theorem subst_teichFam_frobFam (a : R) (n : ℕ) :
    subst (teichFam p a) (frobFam p R n) = subst (frobFam p R) (teichFam p (a ^ p) n) := by
  rw [frobFam_apply, subst_pow (hasSubst_teichFam _), subst_X (hasSubst_teichFam _), teichFam_apply,
    smul_pow, teichFam_apply, subst_smul hasSubst_frobFam, subst_X hasSubst_frobFam, frobFam_apply,
    ← pow_mul, ← pow_mul, mul_comm (p ^ n) p]

omit hp in

theorem subst_teichFam_verFam (a : R) (n : ℕ) :
    subst (teichFam p (a ^ p)) (verFam R n) = subst (verFam R) (teichFam p a n) := by
  rw [teichFam_apply, subst_smul hasSubst_verFam, subst_X hasSubst_verFam]
  cases n with
  | zero =>
    rw [verFam_zero, ← coe_substAlgHom (hasSubst_teichFam _), map_zero, smul_zero]
  | succ n =>
    rw [verFam_succ, subst_X (hasSubst_teichFam _), teichFam_apply, ← pow_mul, ← pow_succ']

omit hp in

theorem subst_curveFam_teichFam (a : R) (n : ℕ) :
    subst (CartierModule.curveFam R) (teichFam p a n) =
      PowerSeries.rescale a (CartierModule.curveFam R n) := by
  rw [teichFam_apply, subst_smul CartierModule.hasSubst_curveFam,
    subst_X CartierModule.hasSubst_curveFam]
  cases n with
  | zero =>
    show (a ^ p ^ 0) • (PowerSeries.X : PowerSeries R) = PowerSeries.rescale a PowerSeries.X
    rw [pow_zero, pow_one, PowerSeries.rescale_X, PowerSeries.smul_eq_C_mul]
  | succ n =>
    show (a ^ p ^ (n + 1)) • (0 : PowerSeries R) = PowerSeries.rescale a 0
    rw [smul_zero, map_zero]

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

def homothety [Φ.IsComm] (a : R) : CartierModule p Φ →+ CartierModule p Φ :=
  precomp (WittLaw.isEndo_teichFam a)

theorem homothety_eq_precomp [Φ.IsComm] (a : R) :
    (homothety a : CartierModule p Φ →+ CartierModule p Φ) = precomp (WittLaw.isEndo_teichFam a) :=
  rfl

@[simp] theorem toPowerSeries_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    (homothety a f).toPowerSeries = fun j => subst (WittLaw.teichFam p a) (f.toPowerSeries j) := rfl

theorem toPowerSeries_homothety_eq_rescale [Φ.IsComm] (a : R) (f : CartierModule p Φ) (j : Fin d) :
    (homothety a f).toPowerSeries j = rescale (fun n => a ^ p ^ n) (f.toPowerSeries j) :=
  WittLaw.subst_teichFam a _

theorem coeff_toPowerSeries_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) (j : Fin d)
    (e : ℕ →₀ ℕ) :
    coeff e ((homothety a f).toPowerSeries j) =
      (e.prod fun n k => (a ^ p ^ n) ^ k) * coeff e (f.toPowerSeries j) := by
  rw [toPowerSeries_homothety_eq_rescale, coeff_rescale]

theorem homothety_one [Φ.IsComm] (f : CartierModule p Φ) : homothety (1 : R) f = f := by
  apply CartierModule.ext
  funext j
  rw [toPowerSeries_homothety, WittLaw.teichFam_one]
  exact congrFun subst_self _

theorem homothety_zero_left [Φ.IsComm] (f : CartierModule p Φ) : homothety (0 : R) f = 0 := by
  apply CartierModule.ext
  funext j
  rw [toPowerSeries_homothety, WittLaw.teichFam_zero]
  exact subst_zero_of_constantCoeff_eq_zero (f.constantCoeff_eq_zero j)

theorem homothety_mul [Φ.IsComm] (a b : R) (f : CartierModule p Φ) :
    homothety (a * b) f = homothety a (homothety b f) := by
  apply CartierModule.ext
  funext j
  show (precomp _ f).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, toPowerSeries_precomp]
  show subst (WittLaw.teichFam p (a * b)) (f.toPowerSeries j) = _
  congr 1
  funext n
  rw [WittLaw.subst_teichFam_teichFam]

theorem homothety_comm [Φ.IsComm] (a b : R) (f : CartierModule p Φ) :
    homothety a (homothety b f) = homothety b (homothety a f) := by
  rw [← homothety_mul, mul_comm, homothety_mul]

theorem homothety_verschiebung [Φ.IsComm] [CharP R p] (a : R) (f : CartierModule p Φ) :
    homothety a (verschiebung f) = verschiebung (homothety (a ^ p) f) := by
  apply CartierModule.ext
  funext j
  show (precomp _ (precomp _ f)).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, precomp_precomp]
  congr 1
  funext n
  exact WittLaw.subst_teichFam_frobFam a n

theorem frobenius_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    frobenius (homothety a f) = homothety (a ^ p) (frobenius f) := by
  apply CartierModule.ext
  funext j
  show (precomp _ (precomp _ f)).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, precomp_precomp]
  congr 1
  funext n
  exact (WittLaw.subst_teichFam_verFam a n).symm

theorem homothety_nsmul [Φ.IsComm] (a : R) (n : ℕ) (f : CartierModule p Φ) :
    homothety a (n • f) = n • homothety a f :=
  map_nsmul _ _ _

theorem map_homothety [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (a : R) (f : CartierModule p Φ) :
    map φ (homothety a f) = homothety a (map φ f) :=
  map_precomp φ _ f

theorem endAct_homothety [Φ.IsComm] (φ : MvFormalGroup.End Φ) (a : R) (f : CartierModule p Φ) :
    endAct φ (homothety a f) = homothety a (endAct φ f) :=
  map_precomp φ _ f

theorem tangent_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    tangent (homothety a f) = a • tangent f := by
  funext j
  rw [tangent_apply, coeff_toPowerSeries_homothety, Pi.smul_apply, tangent_apply, smul_eq_mul,
    Finsupp.prod_single_index (by simp), pow_zero, pow_one, pow_one]

theorem curve_homothety [Φ.IsComm] (a : R) (f : CartierModule p Φ) (j : Fin d) :
    curve (homothety a f) j = PowerSeries.rescale a (curve f j) := by
  rw [curve_apply, toPowerSeries_homothety, curve_apply,
    subst_comp_subst_apply (WittLaw.hasSubst_teichFam a) hasSubst_curveFam,
    PowerSeries.rescale_eq, rescale_eq_subst,
    subst_comp_subst_apply hasSubst_curveFam (HasSubst.smul_X _)]
  congr 1
  funext n
  rw [WittLaw.subst_curveFam_teichFam, PowerSeries.rescale_eq, rescale_eq_subst]

namespace Examples

theorem homothety_addLinear (a : R) (v : Fin d → R) :
    homothety a (addLinear p v) = addLinear p (a • v) := by
  apply CartierModule.ext
  funext i
  rw [toPowerSeries_homothety, toPowerSeries_addLinear]
  show subst (WittLaw.teichFam p a) ((addLinear p v).toPowerSeries i) = _
  rw [toPowerSeries_addLinear, subst_smul (WittLaw.hasSubst_teichFam a),
    subst_X (WittLaw.hasSubst_teichFam a), WittLaw.teichFam_apply, pow_zero, pow_one, smul_smul,
    Pi.smul_apply, smul_eq_mul, mul_comm]

end Examples

end CartierModule

end MvFormalGroup

end


