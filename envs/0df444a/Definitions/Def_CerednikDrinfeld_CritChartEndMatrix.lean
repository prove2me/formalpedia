-- Prove2me | Definitions.Def_CerednikDrinfeld_CritChartEndMatrix
-- name    : CerednikDrinfeld_CritChartEndMatrix
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/0b995abe-fea0-5b9b-b90f-f8a609ff9b2e
-- title:
--   ℤ_p-structure on Cartier modules and critical-chart matrix representation
-- statement:
--   Throughout, $p$ is a prime and $B$ a commutative ring of characteristic $p$. The first group of definitions equips Cartier modules with a $\mathbb Z_p$-structure: `padicIntToWitt` is the ring homomorphism $\mathbb Z_p \to W(B)$ obtained from the inverse of Mathlib's isomorphism $W(\mathbb Z/p)\cong\mathbb Z_p$ followed by the functorial map induced by $\mathbb Z/p \to B$; its image consists of Frobenius-fixed Witt vectors, it is injective for nontrivial $B$, and it is compatible with natural-number casts. Restricting the $W(B)$-action along it gives, for a commutative $d$-dimensional formal group law $\Phi$ over $B$, a $\mathbb Z_p$-module structure on `CartierModule p Φ`, for which the Verschiebung, the Frobenius, the homotheties, and the maps induced by homomorphisms of laws (in particular the action `endAct` of endomorphisms) are all $\mathbb Z_p$-linear; more generally $w\cdot Vf = V(w\cdot f)$ whenever $\mathrm{Frob}(w)=w$.
--
--   For a formal $\mathcal O_D$-module $X$ over $B$, `endOD X` is defined as the centraliser, inside the endomorphism ring of the underlying law `X.F`, of the set consisting of the image of `X.actEnd` together with `X.varpiEnd`; equivalently, of those $f$ commuting with every `X.actEnd a` and with `X.varpiEnd`. Such $f$ act on the Cartier module preserving each graded piece $\{m : \mathrm{endAct}(X.\mathrm{actEnd}(\tau c))\,m = \mathrm{homothety}(j(\tau c)^{p^n})\,m$ for all $c$ in $\mathbb F_{p^2}\}$ attached to a ring homomorphism $j\colon \mathbb{Z}_{p^2}\to B$, and preserving the set `CritChart.invariants X j i`, membership in which amounts to lying in the $i$-th graded piece together with the equation $\mathrm{endAct}(X.\mathrm{varpiEnd})\,m = V m$; also recorded is $V(M_n)\subseteq M_{n+1}$, and that Frobenius-fixed Witt vectors, in particular $\mathbb Z_p$, preserve the invariants. Consequently the invariants form a $\mathbb Z_p$-submodule `invariantsSubmodule X j i`, and `endODInvariants X j i` is the ring homomorphism from `endOD X` to the $\mathbb Z_p$-linear endomorphisms of it sending $f$ to the restriction of `endAct f`. Finally, given a basis $\beta$ of the invariants indexed by a finite type $\iota$, `endMatrix` is the composite ring homomorphism `endOD X` $\to \mathrm{Mat}_{\iota}(\mathbb Z_p)$ taking matrices with respect to $\beta$, with the entry formula $\beta.\mathrm{repr}$ and the expansion $\sum_r (\ldots)_{rs}\,\beta_r$, and `endMatrixQ` is its entrywise base change to $\mathbb Q_p$.
--
--   **Relation to Mathlib.** Witt vectors, the isomorphism $W(\mathbb Z/p)\cong\mathbb Z_p$ (`WittVector.equiv`), the $p$-adic rings and `LinearMap.toMatrixAlgEquiv` are Mathlib's; the Cartier module of a multivariate formal group law, formal $\mathcal O_D$-modules, their graded pieces and the critical-chart invariants are the project's own notions, so `endOD`, `endODInvariants` and the matrix homomorphisms have no Mathlib counterpart.
--
--   **Where it is used.** These definitions set up the explicit chart by which the $\mathcal O_D$-equivariant endomorphisms of a special formal $\mathcal O_D$-module act on a rank-two $\mathbb Z_p$-lattice, namely the $\Pi=V$ invariants in a critical graded piece of the Cartier module, and hence by matrices over $\mathbb Z_p$ and $\mathbb Q_p$. This is the linear-algebra input to Drinfeld's description of special formal $\mathcal O_D$-modules underlying the $p$-adic uniformisation of Shimura curves used on the automorphic side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_CritChartEndMatrix.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace CartierModule

variable (p : ℕ) [hp : Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]

def padicIntToWitt : ℤ_[p] →+* WittVector p R :=
  (WittVector.map (ZMod.castHom (dvd_refl p) R)).comp (WittVector.equiv p).symm.toRingHom

theorem padicIntToWitt_apply (z : ℤ_[p]) :
    padicIntToWitt p R z = WittVector.map (ZMod.castHom (dvd_refl p) R) ((WittVector.equiv p).symm z) :=
  rfl

theorem frobenius_padicIntToWitt (z : ℤ_[p]) :
    WittVector.frobenius (padicIntToWitt p R z) = padicIntToWitt p R z := by
  rw [padicIntToWitt_apply]
  set w := (WittVector.equiv p).symm z
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.map_coeff, ← map_pow, ZMod.pow_card]

theorem padicIntToWitt_injective [Nontrivial R] : Function.Injective (padicIntToWitt p R) :=
  (WittVector.map_injective _ (ZMod.castHom (dvd_refl p) R).injective).comp
    (WittVector.equiv p).symm.injective

theorem padicIntToWitt_natCast (n : ℕ) : padicIntToWitt p R n = n := map_natCast _ n

variable {p R}
variable {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]

instance instModulePadicInt : Module ℤ_[p] (CartierModule p Φ) :=
  Module.compHom (CartierModule p Φ) (padicIntToWitt p R)

theorem padicInt_smul_def (z : ℤ_[p]) (f : CartierModule p Φ) : z • f = padicIntToWitt p R z • f := rfl

theorem map_smul_padicInt {d' : ℕ} {Φ' : MvFormalGroup d' R} [Φ'.IsComm] (φ : Φ.Hom Φ') (z : ℤ_[p])
    (f : CartierModule p Φ) : map φ (z • f) = z • map φ f := by
  rw [padicInt_smul_def, padicInt_smul_def, map_smul_witt]

theorem endAct_smul_padicInt (φ : MvFormalGroup.End Φ) (z : ℤ_[p]) (f : CartierModule p Φ) :
    endAct φ (z • f) = z • endAct φ f :=
  map_smul_padicInt φ z f

theorem verschiebung_smul_padicInt (z : ℤ_[p]) (f : CartierModule p Φ) :
    verschiebung (z • f) = z • verschiebung f := by
  rw [padicInt_smul_def, padicInt_smul_def, smul_verschiebung, frobenius_padicIntToWitt]

theorem frobenius_smul_padicInt (z : ℤ_[p]) (f : CartierModule p Φ) :
    frobenius (z • f) = z • frobenius f := by
  rw [padicInt_smul_def, padicInt_smul_def, frobenius_smul, frobenius_padicIntToWitt]

theorem homothety_smul_padicInt (a : R) (z : ℤ_[p]) (f : CartierModule p Φ) :
    homothety a (z • f) = z • homothety a f := by
  rw [padicInt_smul_def, padicInt_smul_def, homothety_smul_witt]

theorem smul_verschiebung_of_frobenius_eq {w : WittVector p R} (hw : WittVector.frobenius w = w)
    (f : CartierModule p Φ) : w • verschiebung f = verschiebung (w • f) := by
  rw [smul_verschiebung, hw]

end CartierModule

end MvFormalGroup

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

abbrev endOD (X : FormalODModule p B) : Subring (MvFormalGroup.End X.F) :=
  Subring.centralizer (Set.range X.actEnd ∪ {X.varpiEnd})

theorem mem_endOD_iff (X : FormalODModule p B) (f : MvFormalGroup.End X.F) :
    f ∈ endOD X ↔ (∀ a, X.actEnd a * f = f * X.actEnd a) ∧ X.varpiEnd * f = f * X.varpiEnd := by
  rw [endOD, Subring.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun a => h _ (Or.inl ⟨a, rfl⟩), h _ (Or.inr rfl)⟩
  · rintro ⟨ha, hv⟩ g (⟨a, rfl⟩ | hg)
    · exact ha a
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hv

theorem endAct_actEnd_comm {X : FormalODModule p B} {f : MvFormalGroup.End X.F} (hf : f ∈ endOD X)
    (a : Zp2 p) (m : CartierModule p X.F) :
    endAct f (endAct (X.actEnd a) m) = endAct (X.actEnd a) (endAct f m) := by
  show (endAct f * endAct (X.actEnd a) : AddMonoid.End (CartierModule p X.F)) m =
    (endAct (X.actEnd a) * endAct f : AddMonoid.End (CartierModule p X.F)) m
  rw [← map_mul, ← map_mul, ((mem_endOD_iff X f).1 hf).1 a]

theorem endAct_varpiEnd_comm {X : FormalODModule p B} {f : MvFormalGroup.End X.F} (hf : f ∈ endOD X)
    (m : CartierModule p X.F) :
    endAct f (endAct X.varpiEnd m) = endAct X.varpiEnd (endAct f m) := by
  show (endAct f * endAct X.varpiEnd : AddMonoid.End (CartierModule p X.F)) m =
    (endAct X.varpiEnd * endAct f : AddMonoid.End (CartierModule p X.F)) m
  rw [← map_mul, ← map_mul, ((mem_endOD_iff X f).1 hf).2]

theorem endAct_mem_gradedPiece {X : FormalODModule p B} (j : Zp2 p →+* B) {f : MvFormalGroup.End X.F}
    (hf : f ∈ endOD X) (n : ℕ) {m : CartierModule p X.F} (hm : m ∈ X.gradedPiece j n) :
    endAct f m ∈ X.gradedPiece j n := fun c => by
  rw [← endAct_actEnd_comm hf, hm c, endAct_homothety]

variable [CharP B p]

theorem verschiebung_mem_gradedPiece_succ {X : FormalODModule p B} (j : Zp2 p →+* B) (n : ℕ)
    {m : CartierModule p X.F} (hm : m ∈ X.gradedPiece j n) :
    verschiebung m ∈ X.gradedPiece j (n + 1) := fun c => by
  rw [endAct_verschiebung, hm c, homothety_verschiebung, ← pow_mul, ← pow_succ,
    apply_teichmuller_pow_pow_add_two j c n]

theorem endAct_mem_invariants {X : FormalODModule p B} (j : Zp2 p →+* B) {f : MvFormalGroup.End X.F}
    (hf : f ∈ endOD X) (i : ℕ) {m : CartierModule p X.F} (hm : m ∈ CritChart.invariants X j i) :
    endAct f m ∈ CritChart.invariants X j i :=
  ⟨endAct_mem_gradedPiece j hf i hm.1, by rw [← endAct_varpiEnd_comm hf, hm.2, endAct_verschiebung]⟩

theorem smul_witt_mem_invariants_of_frobenius_eq {X : FormalODModule p B} (j : Zp2 p →+* B) (i : ℕ)
    {w : WittVector p B} (hw : WittVector.frobenius w = w) {m : CartierModule p X.F}
    (hm : m ∈ CritChart.invariants X j i) : w • m ∈ CritChart.invariants X j i := by
  refine ⟨fun c => ?_, ?_⟩
  · rw [endAct_smul_witt, hm.1 c, homothety_smul_witt]
  · rw [endAct_smul_witt, hm.2, smul_verschiebung_of_frobenius_eq hw]

theorem smul_padicInt_mem_invariants {X : FormalODModule p B} (j : Zp2 p →+* B) (i : ℕ) (z : ℤ_[p])
    {m : CartierModule p X.F} (hm : m ∈ CritChart.invariants X j i) : z • m ∈ CritChart.invariants X j i :=
  smul_witt_mem_invariants_of_frobenius_eq j i (frobenius_padicIntToWitt p B z) hm

namespace CritChart

def invariantsSubmodule (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    Submodule ℤ_[p] (CartierModule p X.F) where
  carrier := invariants X j i
  zero_mem' := zero_mem _
  add_mem' := add_mem
  smul_mem' z _ hm := smul_padicInt_mem_invariants j i z hm

@[simp] theorem mem_invariantsSubmodule_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (m : CartierModule p X.F) : m ∈ invariantsSubmodule X j i ↔ m ∈ invariants X j i :=
  Iff.rfl

theorem coe_invariantsSubmodule (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    (invariantsSubmodule X j i : Set (CartierModule p X.F)) = invariants X j i := rfl

def endODInvariantsLin (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) (f : endOD X) :
    Module.End ℤ_[p] (invariantsSubmodule X j i) where
  toFun m := ⟨endAct (f : MvFormalGroup.End X.F) m, endAct_mem_invariants j f.2 i m.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' z _ := Subtype.ext (endAct_smul_padicInt _ z _)

@[simp] theorem coe_endODInvariantsLin_apply (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (f : endOD X) (m : invariantsSubmodule X j i) :
    (endODInvariantsLin X j i f m : CartierModule p X.F) = endAct (f : MvFormalGroup.End X.F) m := rfl

def endODInvariants (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    endOD X →+* Module.End ℤ_[p] (invariantsSubmodule X j i) where
  toFun := endODInvariantsLin X j i
  map_one' := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_endODInvariantsLin_apply, OneMemClass.coe_one, map_one]; rfl)
  map_mul' f g := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_endODInvariantsLin_apply, Subring.coe_mul, map_mul]; rfl)
  map_zero' := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_endODInvariantsLin_apply, ZeroMemClass.coe_zero, map_zero]; rfl)
  map_add' f g := LinearMap.ext fun m => Subtype.ext (by
    rw [coe_endODInvariantsLin_apply, Subring.coe_add, map_add]; rfl)

@[simp] theorem coe_endODInvariants_apply (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (f : endOD X) (m : invariantsSubmodule X j i) :
    (endODInvariants X j i f m : CartierModule p X.F) = endAct (f : MvFormalGroup.End X.F) m := rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def endMatrix (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) : endOD X →+* Matrix ι ι ℤ_[p] :=
  (LinearMap.toMatrixAlgEquiv β).toRingEquiv.toRingHom.comp (endODInvariants X j i)

theorem endMatrix_apply (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) (f : endOD X) :
    endMatrix X j i β f = LinearMap.toMatrix β β (endODInvariants X j i f) := rfl

theorem endMatrix_apply_eq_repr (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) (f : endOD X) (r s : ι) :
    endMatrix X j i β f r s = β.repr (endODInvariants X j i f (β s)) r := by
  rw [endMatrix_apply, LinearMap.toMatrix_apply]

theorem sum_endMatrix_smul (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) (f : endOD X) (s : ι) :
    ∑ r, endMatrix X j i β f r s • β r = endODInvariants X j i f (β s) := by
  simp_rw [endMatrix_apply_eq_repr]
  exact β.sum_repr _

def endMatrixQ (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) : endOD X →+* Matrix ι ι ℚ_[p] :=
  (algebraMap ℤ_[p] ℚ_[p]).mapMatrix.comp (endMatrix X j i β)

theorem endMatrixQ_apply (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ)
    (β : Module.Basis ι ℤ_[p] (invariantsSubmodule X j i)) (f : endOD X) :
    endMatrixQ X j i β f = (endMatrix X j i β f).map ((↑) : ℤ_[p] → ℚ_[p]) := rfl

end CritChart

end FormalODModule

end CerednikDrinfeld

end


