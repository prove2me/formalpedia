-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing__EvenBarker
-- name    : OAI_LinearAlgebra_CirculantHadamard_CyclicRing__EvenBarker
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:39:51.913358+00:00
-- url     : https://prove2.me/theorems/7822491b-3d19-44dd-b9d4-4464b814418c
-- title:
--   The cyclic group ring with its involution and augmentation
-- statement:
--   These notions belong to a formal proof that a real circulant Hadamard matrix of positive order $n$ exists only for $n=1$ and $n=4$. Such a matrix has entries $\pm1$, satisfies $HH^{\mathsf T}=nI$, and has the form $H_{ij}=h(j-i)$ with indices in $\mathbb Z/n$. Its first row becomes an element $f$ of the integer group ring $\mathbb Z[\mathbb Z/n]$ with $f f^{*}=n$, where $f^{*}$ reverses the indices. Two-adic descent reduces every order $n>1$ to $n=4u^2$ with $u$ odd; for $u>1$, evaluation at characters with values in cyclotomic rings and a local argument at a prime above $2$ give a contradiction.
--
--   1. **Cyclic group ring.** $R[\mathbb Z/n]$ is the additive monoid algebra of $\mathbb Z/n$ over $R$: finitely supported functions on $\mathbb Z/n$, with product the convolution
--   $$
--   (fg)(a)=\sum_{j\in\mathbb Z/n}f(j)\,g(a-j).
--   $$
--   An element can be built from any coefficient function on $\mathbb Z/n$, and the scalar $r$ is the element $r\,e_0$ supported at $0$.
--   2. **Involution.** For a coefficient ring with a star operation and any finite additive group, $f^{*}(a)=\overline{f(-a)}$. It is involutive and additive, fixes $1$, sends $e_a$ with coefficient $r$ to $e_{-a}$ with coefficient $\bar r$, and satisfies $(fg)^{*}=g^{*}f^{*}$; over a commutative ring it is a ring homomorphism.
--   3. **Augmentation.** The ring homomorphism $\varepsilon(f)=\sum_af(a)$, the sum of all coefficients; it sends the scalar $r$ to $r$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/CyclicRing.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/CyclicRing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EvenBarker mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_PeriodicModFour
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses__EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge__EvenBarker

namespace OAI

universe uR uG

/-! The finite cyclic group ring, with coefficient conjugation and index reversal. -/

namespace CirculantHadamard.CyclicRing

open scoped BigOperators

abbrev Elem (R : Type uR) [Semiring R] (n : ℕ) := AddMonoidAlgebra R (ZMod n)

noncomputable def groupStar {R : Type uR} {G : Type uG} [Semiring R] [StarRing R]
    [AddGroup G] [Fintype G] (f : AddMonoidAlgebra R G) : AddMonoidAlgebra R G :=
  AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun a => star (f.coeff (-a)))

@[simp] theorem groupStar_apply {R : Type uR} {G : Type uG} [Semiring R] [StarRing R]
    [AddGroup G] [Fintype G] (f : AddMonoidAlgebra R G) (a : G) :
    (groupStar f).coeff a = star (f.coeff (-a)) := rfl

@[simp] theorem groupStar_groupStar {R : Type uR} {G : Type uG} [Semiring R] [StarRing R]
    [AddGroup G] [Fintype G] (f : AddMonoidAlgebra R G) :
    groupStar (groupStar f) = f := by
  ext a
  simp

@[simp] theorem groupStar_single {R : Type uR} {G : Type uG} [Semiring R] [StarRing R]
    [AddGroup G] [Fintype G] (a : G) (r : R) :
    groupStar (AddMonoidAlgebra.single a r) = AddMonoidAlgebra.single (-a) (star r) := by
  classical
  ext b
  change star (Finsupp.single a r (-b)) = Finsupp.single (-a) (star r) b
  by_cases hb : b = -a
  · subst b
    simp
  · have hab : a ≠ -b := by
      intro h
      apply hb
      simpa using (congrArg (fun x : G => -x) h).symm
    simp [hab, Ne.symm hb]

noncomputable def ofCoeffs {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (c : ZMod n → R) : Elem R n :=
  AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c)

@[simp] theorem ofCoeffs_apply {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (c : ZMod n → R) (a : ZMod n) : (ofCoeffs c).coeff a = c a := rfl

@[simp] theorem ofCoeffs_coeffs {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f : Elem R n) : ofCoeffs (fun a => f.coeff a) = f := by
  exact AddMonoidAlgebra.coeff_injective (Finsupp.ext fun _ => rfl)

noncomputable def scalar {R : Type uR} [Semiring R] (n : ℕ) (r : R) : Elem R n :=
  AddMonoidAlgebra.single 0 r

@[simp] theorem scalar_apply {R : Type uR} [Semiring R] {n : ℕ}
    (r : R) (a : ZMod n) : (scalar n r).coeff a = if a = 0 then r else 0 := by
  classical
  simp [scalar, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]

@[simp] theorem scalar_natCast {R : Type uR} [Semiring R] (n m : ℕ) :
    scalar n (m : R) = (m : Elem R n) := rfl

noncomputable def ringStar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) : Elem R n :=
  ofCoeffs fun a => star (f.coeff (-a))

@[simp] theorem ringStar_apply {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) (a : ZMod n) :
    (ringStar f).coeff a = star (f.coeff (-a)) := rfl

@[simp] theorem ringStar_single {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (a : ZMod n) (r : R) :
    ringStar (AddMonoidAlgebra.single a r) = AddMonoidAlgebra.single (-a) (star r) :=
  groupStar_single a r

section Convolution

variable {R : Type uR} {G : Type uG} [Semiring R] [AddCommGroup G] [Fintype G]

theorem group_mul_apply (f g : AddMonoidAlgebra R G) (a : G) :
    (f * g).coeff a = ∑ j, f.coeff j * g.coeff (a - j) := by
  classical
  calc
    (f * g).coeff a = f.coeff.sum (fun j r => r * g.coeff (-j + a)) :=
      AddMonoidAlgebra.coeff_mul_apply_left f g a
    _ = ∑ j, f.coeff j * g.coeff (-j + a) := Finsupp.sum_fintype _ _ (fun _ => zero_mul _)
    _ = _ := by simp only [sub_eq_add_neg, add_comm]

theorem group_mul_apply_right (f g : AddMonoidAlgebra R G) (a : G) :
    (f * g).coeff a = ∑ j, f.coeff (a - j) * g.coeff j := by
  classical
  calc
    (f * g).coeff a = g.coeff.sum (fun j r => f.coeff (a - j) * r) := by
      simpa only [sub_eq_add_neg] using AddMonoidAlgebra.coeff_mul_apply_right f g a
    _ = _ := Finsupp.sum_fintype _ _ (fun _ => mul_zero _)

@[simp] theorem groupStar_zero [StarRing R] :
    groupStar (0 : AddMonoidAlgebra R G) = 0 := by
  ext a
  simp

@[simp] theorem groupStar_add [StarRing R] (f g : AddMonoidAlgebra R G) :
    groupStar (f + g) = groupStar f + groupStar g := by
  ext a
  change star (f.coeff (-a) + g.coeff (-a)) = star (f.coeff (-a)) + star (g.coeff (-a))
  exact star_add _ _

@[simp] theorem groupStar_one [StarRing R] :
    groupStar (1 : AddMonoidAlgebra R G) = 1 := by
  classical
  ext a
  simp [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem groupStar_mul [StarRing R] (f g : AddMonoidAlgebra R G) :
    groupStar (f * g) = groupStar g * groupStar f := by
  ext a
  rw [groupStar_apply, group_mul_apply_right, star_sum, group_mul_apply]
  apply Fintype.sum_equiv (Equiv.neg G)
  intro j
  simp only [star_mul, groupStar_apply, Equiv.neg_apply, neg_neg]
  congr 2
  congr 1
  abel

end Convolution

@[simp] theorem ringStar_ringStar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) : ringStar (ringStar f) = f :=
  groupStar_groupStar f

@[simp] theorem ringStar_zero {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] : ringStar (0 : Elem R n) = 0 := groupStar_zero

@[simp] theorem ringStar_add {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f g : Elem R n) : ringStar (f + g) = ringStar f + ringStar g :=
  groupStar_add f g

@[simp] theorem ringStar_one {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] : ringStar (1 : Elem R n) = 1 := groupStar_one

@[simp] theorem ringStar_scalar {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (r : R) : ringStar (scalar n r) = scalar n (star r) := by
  classical
  ext a
  by_cases ha : a = 0 <;> simp [scalar_apply, ha]

noncomputable def groupStarRingHom {R : Type uR} {G : Type uG} [CommSemiring R] [StarRing R]
    [AddCommGroup G] [Fintype G] : AddMonoidAlgebra R G →+* AddMonoidAlgebra R G where
  toFun := groupStar
  map_zero' := groupStar_zero
  map_one' := groupStar_one
  map_add' := groupStar_add
  map_mul' f g := by rw [groupStar_mul, mul_comm]

noncomputable def ringStarRingHom {R : Type uR} [CommSemiring R] [StarRing R]
    (n : ℕ) [NeZero n] : Elem R n →+* Elem R n := groupStarRingHom

@[simp] theorem ringStarRingHom_apply {R : Type uR} [CommSemiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) : ringStarRingHom n f = ringStar f := rfl

noncomputable def augmentation {R : Type uR} [Semiring R] (n : ℕ) : Elem R n →+* R :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id R) 1 (fun _ _ => Commute.one_right _)

theorem augmentation_apply {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f : Elem R n) : augmentation n f = ∑ a, f.coeff a := by
  change f.coeff.sum (fun _ r => r * 1) = _
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  simp

@[simp] theorem augmentation_scalar {R : Type uR} [Semiring R] (n : ℕ) (r : R) :
    augmentation n (scalar n r) = r := by
  change AddMonoidAlgebra.liftNC (RingHom.id R).toAddMonoidHom
    (1 : Multiplicative (ZMod n) →* R) (AddMonoidAlgebra.single 0 r) = r
  simp

end CirculantHadamard.CyclicRing

end OAI


