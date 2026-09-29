-- Prove2me | Definitions.Def_Dieudonne_WittHomColimit
-- name    : Dieudonne_WittHomColimit
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/33c05b68-1c14-5bd2-be9e-f2ac2ecfe073
-- title:
--   Dieudonné module as colimit of truncated Witt homomorphism groups
-- statement:
--   Fix a prime $p$, a commutative ring $R$ and a commutative $R$-bialgebra $A$. For $n \le m$ the additive map `TruncWitt.shiftLE` sends a truncated Witt vector of length $n$ over a commutative ring to one of length $m$: it is obtained by lifting along the surjection `WittVector.truncate n` the map $x \mapsto$ `truncate m` $(V^{m-n}x)$, where $V^{k}$ is the $k$-fold iterate `verschiebungIter k` of Mathlib's Verschiebung on $W(R)$; on coefficients it is the shift $(\mathrm{shiftLE}\,x)_i = x_{i-(m-n)}$ for $i \ge m-n$ and $0$ otherwise. It is injective, reduces to `TruncWitt.shift` when $m = n+1$, is transitive in $n \le m \le l$, commutes with coefficientwise ring maps, with the $p$-power map `frobeniusFun` and with `verschiebung`; moreover $V^{n} = 0$ on length-$n$ vectors, and $p^{n}\cdot x = 0$ when $p = 0$ in the base.
--
--   The subgroup `wittHom R p n A` of primitive length-$n$ Witt vectors (those $x$ with $\Delta_*x = (\mathrm{incl}_L)_*x + (\mathrm{incl}_R)_*x$ in $W_n(A \otimes_R A)$) is stable under `shiftLE`, indeed $x$ is primitive if and only if its shift is, giving `wittHomShiftLE` and a directed system over $(\mathbb{N},\le)$. `DieudonneModule R p A` is the direct limit of this system as an abelian group, with structure maps `of R p A n`, each injective, jointly surjective, with $\mathrm{of}\,m \circ \mathrm{shiftLE} = \mathrm{of}\,n$; a universal property `lift` requires compatibility only with the successor maps `wittHomShift`. Passing to the limit gives endomorphisms `verschiebung` and, when $R$ has characteristic $p$, `frobenius`, with $FV = VF = p$; these are packaged as a term `dieudonneDatum` of the project's structure `DieudonneDatum` with parameter $(p : \mathbb{Z})$, whose two commutation identities are fields. In characteristic $p$ every element is killed by some $p^{n}$. A bialgebra map $\varphi : A \to B$ induces `map`, functorial in $\varphi$, commuting with $F$ and $V$, and injective for injective $\varphi$. Finally, for $A$ the symmetric algebra on $R$ (the additive group), the canonical coordinate gives a primitive length-$1$ Witt vector whose image in the limit is nonzero when $R$ is nontrivial.
--
--   **Relation to Mathlib.** Mathlib supplies `WittVector`, `TruncatedWittVector`, their truncation maps and Verschiebung, and the direct limit `AddCommGroup.DirectLimit`; the shift maps between different truncation lengths, the primitive subgroups `wittHom`, and the Dieudonné module itself are the project's own, Mathlib having no Dieudonné theory.
--
--   **Where it is used.** These groups provide the Dieudonné-module functor on commutative affine group schemes used in the study of finite flat group schemes attached to the mod $p$ and $p$-adic representations occurring in the modularity-lifting part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Dieudonne_WittHomColimit.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Function

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n m l : ℕ}
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

noncomputable def verschiebungIter (k : ℕ) : WittVector p R →+ WittVector p R where
  toFun x := (WittVector.verschiebung (p := p) (R := R))^[k] x
  map_zero' := iterate_map_zero _ _
  map_add' := iterate_map_add _ _

@[simp] theorem verschiebungIter_apply (k : ℕ) (x : WittVector p R) :
    verschiebungIter k x = (WittVector.verschiebung (p := p) (R := R))^[k] x := rfl

noncomputable def shiftLE (h : n ≤ m) :
    TruncatedWittVector p n R →+ TruncatedWittVector p m R :=
  AddMonoidHom.liftOfRightInverse (WittVector.truncate n).toAddMonoidHom TruncatedWittVector.out
    (fun x => TruncatedWittVector.truncateFun_out x)
    ⟨(WittVector.truncate m).toAddMonoidHom.comp (verschiebungIter (m - n)),
      fun x hx => by
        change (WittVector.truncate n) x = 0 at hx
        rw [← RingHom.mem_ker, WittVector.mem_ker_truncate] at hx
        change (WittVector.truncate m) ((WittVector.verschiebung (p := p) (R := R))^[m - n] x) = 0
        ext ⟨i, hi⟩
        simp only [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
        by_cases him : i < m - n
        · exact WittVector.iterate_verschiebung_coeff_eq_zero x him
        · obtain ⟨k, rfl⟩ : ∃ k, i = k + (m - n) := ⟨i - (m - n), by omega⟩
          rw [WittVector.iterate_verschiebung_coeff]
          exact hx k (by omega)⟩

@[simp] theorem shiftLE_truncate (h : n ≤ m) (x : WittVector p R) :
    shiftLE h (WittVector.truncate n x) =
      WittVector.truncate m ((WittVector.verschiebung (p := p) (R := R))^[m - n] x) :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _
    (fun x => TruncatedWittVector.truncateFun_out x) _ _

theorem coeff_shiftLE (h : n ≤ m) (x : TruncatedWittVector p n R) (i : Fin m) :
    (shiftLE h x).coeff i =
      if hi : m - n ≤ (i : ℕ) then x.coeff ⟨i - (m - n), by omega⟩ else 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shiftLE_truncate, WittVector.coeff_truncate]
  split_ifs with hi
  · rw [WittVector.coeff_truncate]
    have hk : (i : ℕ) = (i - (m - n)) + (m - n) := by omega
    conv_lhs => rw [hk]
    exact WittVector.iterate_verschiebung_coeff x (m - n) _
  · exact WittVector.iterate_verschiebung_coeff_eq_zero x (by omega)

theorem coeff_shiftLE_of_lt (h : n ≤ m) (x : TruncatedWittVector p n R) (i : Fin m)
    (hi : (i : ℕ) < m - n) : (shiftLE h x).coeff i = 0 := by
  rw [coeff_shiftLE, dif_neg (by omega)]

theorem coeff_shiftLE_add (h : n ≤ m) (x : TruncatedWittVector p n R) (i : Fin n) :
    (shiftLE h x).coeff ⟨i + (m - n), by omega⟩ = x.coeff i := by
  rw [coeff_shiftLE, dif_pos (by simp)]
  congr 1
  ext
  simp

@[simp] theorem shiftLE_refl (x : TruncatedWittVector p n R) : shiftLE le_rfl x = x :=
  TruncatedWittVector.ext fun i => by
    rw [coeff_shiftLE, dif_pos (by simp)]
    congr 1
    exact Fin.ext (by simp)

theorem shiftLE_shiftLE (h₁ : n ≤ m) (h₂ : m ≤ l) (x : TruncatedWittVector p n R) :
    shiftLE h₂ (shiftLE h₁ x) = shiftLE (h₁.trans h₂) x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shiftLE_truncate, shiftLE_truncate, shiftLE_truncate, ← Function.iterate_add_apply]
  congr 2
  omega

theorem shiftLE_succ (x : TruncatedWittVector p n R) :
    shiftLE (Nat.le_succ n) x = shift x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shiftLE_truncate, shift_truncate, Nat.succ_sub (le_refl n), Nat.sub_self,
    Function.iterate_one]

theorem shiftLE_injective (h : n ≤ m) : Injective (shiftLE (p := p) (R := R) h) :=
  fun x y hxy => TruncatedWittVector.ext fun i => by
    rw [← coeff_shiftLE_add h x i, ← coeff_shiftLE_add h y i, hxy]

theorem map_shiftLE (f : R →+* S) (h : n ≤ m) (x : TruncatedWittVector p n R) :
    map f (shiftLE h x) = shiftLE h (map f x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_map, coeff_shiftLE]
    split_ifs
    · rfl
    · exact map_zero f

theorem frobeniusFun_shiftLE (h : n ≤ m) (x : TruncatedWittVector p n R) :
    frobeniusFun (shiftLE h x) = shiftLE h (frobeniusFun x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_frobeniusFun, coeff_shiftLE]
    split_ifs
    · rfl
    · exact zero_pow hp.out.ne_zero

theorem verschiebung_shiftLE (h : n ≤ m) (x : TruncatedWittVector p n R) :
    verschiebung (shiftLE h x) = shiftLE h (verschiebung x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [shiftLE_truncate, verschiebung_truncate, verschiebung_truncate, shiftLE_truncate,
    ← Function.iterate_succ_apply' (f := WittVector.verschiebung),
    Function.iterate_succ_apply (f := WittVector.verschiebung)]

theorem verschiebung_iterate_eq_zero (x : TruncatedWittVector p n R) :
    (verschiebung (p := p) (R := R))^[n] x = 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  have key : ∀ k : ℕ, (verschiebung (p := p) (n := n) (R := R))^[k] (WittVector.truncate n x) =
      WittVector.truncate n ((WittVector.verschiebung (p := p) (R := R))^[k] x) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, verschiebung_truncate,
        ← Function.iterate_succ_apply' (f := WittVector.verschiebung)]
  rw [key]
  ext ⟨i, hi⟩
  rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
  exact WittVector.iterate_verschiebung_coeff_eq_zero x hi

theorem pow_card_nsmul_eq_zero (hR : (p : R) = 0) (x : TruncatedWittVector p n R) :
    p ^ n • x = 0 := by
  rcases subsingleton_or_charP hR with h | h
  · exact Subsingleton.elim _ _
  · obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
    rw [← map_nsmul, nsmul_eq_mul, Nat.cast_pow, mul_comm,
      ← WittVector.iterate_verschiebung_iterate_frobenius]
    ext ⟨i, hi⟩
    rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
    exact WittVector.iterate_verschiebung_coeff_eq_zero _ hi

end TruncWitt

section WittHom

variable {R : Type u} [CommRing R] {p : ℕ} [hp : Fact p.Prime] {n m l : ℕ}
variable {A : Type v} [CommRing A] [Bialgebra R A]

open TruncWitt

theorem shiftLE_mem_wittHom (h : n ≤ m) {x : TruncatedWittVector p n A}
    (hx : x ∈ wittHom R p n A) : TruncWitt.shiftLE h x ∈ wittHom R p m A := by
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_shiftLE, map_shiftLE, map_shiftLE, hx, map_add]

theorem shiftLE_mem_wittHom_iff (h : n ≤ m) (x : TruncatedWittVector p n A) :
    TruncWitt.shiftLE h x ∈ wittHom R p m A ↔ x ∈ wittHom R p n A := by
  refine ⟨fun hx => ?_, shiftLE_mem_wittHom h⟩
  rw [mem_wittHom_iff] at hx ⊢
  rw [map_shiftLE, map_shiftLE, map_shiftLE, ← map_add] at hx
  exact shiftLE_injective h hx

variable (R p A) in

noncomputable def wittHomShiftLE (h : n ≤ m) : wittHom R p n A →+ wittHom R p m A where
  toFun x := ⟨TruncWitt.shiftLE h x, shiftLE_mem_wittHom h x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_wittHomShiftLE (h : n ≤ m) (x : wittHom R p n A) :
    (wittHomShiftLE R p A h x : TruncatedWittVector p m A) = TruncWitt.shiftLE h x := rfl

@[simp] theorem wittHomShiftLE_refl (x : wittHom R p n A) : wittHomShiftLE R p A le_rfl x = x :=
  Subtype.ext (shiftLE_refl _)

theorem wittHomShiftLE_shiftLE (h₁ : n ≤ m) (h₂ : m ≤ l) (x : wittHom R p n A) :
    wittHomShiftLE R p A h₂ (wittHomShiftLE R p A h₁ x) = wittHomShiftLE R p A (h₁.trans h₂) x :=
  Subtype.ext (shiftLE_shiftLE h₁ h₂ _)

theorem wittHomShiftLE_succ (x : wittHom R p n A) :
    wittHomShiftLE R p A (Nat.le_succ n) x = wittHomShift R p n A x :=
  Subtype.ext (shiftLE_succ _)

theorem wittHomShiftLE_injective (h : n ≤ m) : Injective (wittHomShiftLE R p A h) :=
  fun _ _ hxy => Subtype.ext (shiftLE_injective h (congrArg Subtype.val hxy))

theorem wittHomShiftLE_verschiebung (h : n ≤ m) (x : wittHom R p n A) :
    wittHomShiftLE R p A h (wittHomVerschiebung R p n A x) =
      wittHomVerschiebung R p m A (wittHomShiftLE R p A h x) :=
  Subtype.ext (verschiebung_shiftLE h _).symm

theorem wittHomShiftLE_frobenius [CharP R p] (h : n ≤ m) (x : wittHom R p n A) :
    wittHomShiftLE R p A h (wittHomFrobenius R p n A x) =
      wittHomFrobenius R p m A (wittHomShiftLE R p A h x) :=
  Subtype.ext (frobeniusFun_shiftLE h _).symm

theorem wittHomMap_shiftLE {B : Type w} [CommRing B] [Bialgebra R B] (φ : A →ₐc[R] B)
    (h : n ≤ m) (x : wittHom R p n A) :
    wittHomMap p m φ (wittHomShiftLE R p A h x) = wittHomShiftLE R p B h (wittHomMap p n φ x) :=
  Subtype.ext (map_shiftLE _ h _)

theorem wittHomVerschiebung_iterate_eq_zero (x : wittHom R p n A) :
    (wittHomVerschiebung R p n A)^[n] x = 0 := by
  apply Subtype.ext
  have : ∀ k : ℕ, (((wittHomVerschiebung R p n A)^[k] x : wittHom R p n A) :
      TruncatedWittVector p n A) = (TruncWitt.verschiebung (p := p) (R := A))^[k] x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl
  rw [this]
  exact verschiebung_iterate_eq_zero _

theorem pow_nsmul_wittHom_eq_zero [CharP R p] (x : wittHom R p n A) : p ^ n • x = 0 :=
  Subtype.ext (by
    rw [AddSubgroupClass.coe_nsmul, ZeroMemClass.coe_zero]
    exact pow_card_nsmul_eq_zero (natCast_eq_zero_of_algebra R p A) _)

instance wittHomShiftLE_directedSystem :
    DirectedSystem (fun n => ↥(wittHom R p n A)) fun _ _ h => wittHomShiftLE R p A h where
  map_self _ x := wittHomShiftLE_refl x
  map_map _ _ _ h₁ h₂ x := wittHomShiftLE_shiftLE h₁ h₂ x

end WittHom

section Colimit

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra R A]

def DieudonneModule : Type v :=
  AddCommGroup.DirectLimit (fun n => ↥(wittHom R p n A)) fun _ _ h => wittHomShiftLE R p A h

namespace DieudonneModule

noncomputable instance instAddCommGroup : AddCommGroup (DieudonneModule R p A) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (fun n => ↥(wittHom R p n A)) fun _ _ h => wittHomShiftLE R p A h))

noncomputable instance instInhabited : Inhabited (DieudonneModule R p A) := ⟨0⟩

noncomputable def of (n : ℕ) : wittHom R p n A →+ DieudonneModule R p A :=
  AddCommGroup.DirectLimit.of (fun n => ↥(wittHom R p n A)) (fun _ _ h => wittHomShiftLE R p A h) n

variable {R p A}
variable {n m : ℕ}

@[simp] theorem of_shiftLE (h : n ≤ m) (x : wittHom R p n A) :
    of R p A m (wittHomShiftLE R p A h x) = of R p A n x :=
  AddCommGroup.DirectLimit.of_f _ _

@[simp] theorem of_shift (x : wittHom R p n A) :
    of R p A (n + 1) (wittHomShift R p n A x) = of R p A n x := by
  rw [← wittHomShiftLE_succ, of_shiftLE]

@[elab_as_elim]
protected theorem induction_on {C : DieudonneModule R p A → Prop} (z : DieudonneModule R p A)
    (ih : ∀ (n : ℕ) (x : wittHom R p n A), C (of R p A n x)) : C z :=
  AddCommGroup.DirectLimit.induction_on z ih

theorem exists_of (z : DieudonneModule R p A) : ∃ (n : ℕ) (x : wittHom R p n A), of R p A n x = z :=
  DieudonneModule.induction_on z fun n x => ⟨n, x, rfl⟩

theorem exists_shiftLE_eq_zero_of_of_eq_zero {x : wittHom R p n A} (hx : of R p A n x = 0) :
    ∃ (m : ℕ) (h : n ≤ m), wittHomShiftLE R p A h x = 0 :=
  AddCommGroup.DirectLimit.of.zero_exact (f := fun _ _ h => wittHomShiftLE R p A h) n x hx

theorem of_injective (n : ℕ) : Injective (of R p A n) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨m, h, hm⟩ := exists_shiftLE_eq_zero_of_of_eq_zero hx
  exact wittHomShiftLE_injective h (by rw [hm, map_zero])

theorem of_eq_of_iff (x : wittHom R p n A) (y : wittHom R p m A) :
    of R p A n x = of R p A m y ↔
      wittHomShiftLE R p A (le_max_left n m) x = wittHomShiftLE R p A (le_max_right n m) y := by
  constructor
  · intro h
    apply of_injective (max n m)
    rwa [of_shiftLE, of_shiftLE]
  · intro h
    rw [← of_shiftLE (le_max_left n m) x, h, of_shiftLE]

section Lift

variable {P : Type w} [AddCommGroup P]

theorem compat_shiftLE (g : ∀ n, wittHom R p n A →+ P)
    (hg : ∀ (n : ℕ) (x : wittHom R p n A), g (n + 1) (wittHomShift R p n A x) = g n x)
    (h : n ≤ m) (x : wittHom R p n A) : g m (wittHomShiftLE R p A h x) = g n x := by
  induction h with
  | refl => rw [wittHomShiftLE_refl]
  | @step m h ih =>
    rw [← wittHomShiftLE_shiftLE h (Nat.le_succ m), wittHomShiftLE_succ, hg, ih]

variable (R p A) in

noncomputable def lift (g : ∀ n, wittHom R p n A →+ P)
    (hg : ∀ (n : ℕ) (x : wittHom R p n A), g (n + 1) (wittHomShift R p n A x) = g n x) :
    DieudonneModule R p A →+ P :=
  AddCommGroup.DirectLimit.lift (fun n => ↥(wittHom R p n A)) (fun _ _ h => wittHomShiftLE R p A h)
    P g fun _ _ h x => compat_shiftLE g hg h x

@[simp] theorem lift_of (g : ∀ n, wittHom R p n A →+ P)
    (hg : ∀ (n : ℕ) (x : wittHom R p n A), g (n + 1) (wittHomShift R p n A x) = g n x)
    (x : wittHom R p n A) : lift R p A g hg (of R p A n x) = g n x :=
  AddCommGroup.DirectLimit.lift_of _ _ _ _ _

theorem hom_ext {f g : DieudonneModule R p A →+ P}
    (h : ∀ (n : ℕ) (x : wittHom R p n A), f (of R p A n x) = g (of R p A n x)) : f = g :=
  AddMonoidHom.ext fun z => DieudonneModule.induction_on z h

end Lift

variable (R p A) in

noncomputable def verschiebung : DieudonneModule R p A →+ DieudonneModule R p A :=
  lift R p A (fun n => (of R p A n).comp (wittHomVerschiebung R p n A)) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← wittHomShift_verschiebung, of_shift]

@[simp] theorem verschiebung_of (x : wittHom R p n A) :
    verschiebung R p A (of R p A n x) = of R p A n (wittHomVerschiebung R p n A x) :=
  lift_of _ _ _

section CharP

variable [CharP R p]

variable (R p A) in

noncomputable def frobenius : DieudonneModule R p A →+ DieudonneModule R p A :=
  lift R p A (fun n => (of R p A n).comp (wittHomFrobenius R p n A)) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← wittHomShift_frobenius, of_shift]

@[simp] theorem frobenius_of (x : wittHom R p n A) :
    frobenius R p A (of R p A n x) = of R p A n (wittHomFrobenius R p n A x) :=
  lift_of _ _ _

theorem frobenius_verschiebung (z : DieudonneModule R p A) :
    frobenius R p A (verschiebung R p A z) = (p : ℤ) • z := by
  induction z using DieudonneModule.induction_on with
  | ih n x => rw [verschiebung_of, frobenius_of, wittHomFrobenius_verschiebung, map_zsmul]

theorem verschiebung_frobenius (z : DieudonneModule R p A) :
    verschiebung R p A (frobenius R p A z) = (p : ℤ) • z := by
  induction z using DieudonneModule.induction_on with
  | ih n x => rw [frobenius_of, verschiebung_of, wittHomVerschiebung_frobenius, map_zsmul]

variable (R p A) in

noncomputable def dieudonneDatum : DieudonneDatum (p : ℤ) (DieudonneModule R p A) where
  F := (frobenius R p A).toIntLinearMap
  V := (verschiebung R p A).toIntLinearMap
  fv := LinearMap.ext fun z => frobenius_verschiebung z
  vf := LinearMap.ext fun z => verschiebung_frobenius z

@[simp] theorem dieudonneDatum_F_apply (z : DieudonneModule R p A) :
    (dieudonneDatum R p A).F z = frobenius R p A z := rfl

@[simp] theorem dieudonneDatum_V_apply (z : DieudonneModule R p A) :
    (dieudonneDatum R p A).V z = verschiebung R p A z := rfl

theorem pow_nsmul_of (x : wittHom R p n A) : p ^ n • of R p A n x = 0 := by
  rw [← map_nsmul, pow_nsmul_wittHom_eq_zero, map_zero]

theorem exists_pow_nsmul_eq_zero (z : DieudonneModule R p A) : ∃ n : ℕ, p ^ n • z = 0 := by
  obtain ⟨n, x, rfl⟩ := exists_of z
  exact ⟨n, pow_nsmul_of x⟩

end CharP

section Map

variable {B : Type w} [CommRing B] [Bialgebra R B]

variable (R p) in

noncomputable def map (φ : A →ₐc[R] B) : DieudonneModule R p A →+ DieudonneModule R p B :=
  lift R p A (fun n => (of R p B n).comp (wittHomMap p n φ)) fun n x => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, wittHomMap_shift, of_shift]

@[simp] theorem map_of (φ : A →ₐc[R] B) (x : wittHom R p n A) :
    map R p φ (of R p A n x) = of R p B n (wittHomMap p n φ x) :=
  lift_of _ _ _

theorem map_verschiebung (φ : A →ₐc[R] B) (z : DieudonneModule R p A) :
    map R p φ (verschiebung R p A z) = verschiebung R p B (map R p φ z) := by
  induction z using DieudonneModule.induction_on with
  | ih n x => rw [verschiebung_of, map_of, map_of, verschiebung_of, wittHomMap_verschiebung]

theorem map_frobenius [CharP R p] (φ : A →ₐc[R] B) (z : DieudonneModule R p A) :
    map R p φ (frobenius R p A z) = frobenius R p B (map R p φ z) := by
  induction z using DieudonneModule.induction_on with
  | ih n x => rw [frobenius_of, map_of, map_of, frobenius_of, wittHomMap_frobenius]

theorem map_id (z : DieudonneModule R p A) : map R p (BialgHom.id R A) z = z := by
  induction z using DieudonneModule.induction_on with
  | ih n x =>
    rw [map_of]
    congr 1
    exact Subtype.ext (TruncWitt.map_id _)

theorem map_comp {C : Type*} [CommRing C] [Bialgebra R C] (φ : A →ₐc[R] B) (ψ : B →ₐc[R] C)
    (z : DieudonneModule R p A) : map R p (ψ.comp φ) z = map R p ψ (map R p φ z) := by
  induction z using DieudonneModule.induction_on with
  | ih n x =>
    rw [map_of, map_of, map_of]
    congr 1
    refine Subtype.ext (TruncatedWittVector.ext fun i => ?_)
    simp only [coe_wittHomMap, TruncWitt.coeff_map]
    rfl

theorem map_injective {φ : A →ₐc[R] B} (hφ : Injective φ) : Injective (map R p φ) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨n, x, rfl⟩ := exists_of z
  rw [map_of] at hz
  have hx : wittHomMap p n φ x = 0 := of_injective n (by rw [hz, map_zero])
  rw [wittHomMap_injective hφ (hx.trans (map_zero _).symm), map_zero]

end Map

end DieudonneModule

end Colimit

namespace DieudonneModule.Examples

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime]

abbrev Ga : Type u := SymmetricAlgebra R R

noncomputable def coordinate : Ga R := SymmetricAlgebra.ι R R 1

theorem coordinate_ne_zero [Nontrivial R] : coordinate R ≠ 0 := by
  intro h
  have := congrArg (SymmetricAlgebra.lift (LinearMap.id : R →ₗ[R] R)) h
  rw [coordinate, SymmetricAlgebra.lift_ι_apply, map_zero, LinearMap.id_apply] at this
  exact one_ne_zero this

theorem coeff_zero_add_of_length_one {S : Type v} [CommRing S] (x y : TruncatedWittVector p 1 S) :
    (x + y).coeff 0 = x.coeff 0 + y.coeff 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p 1 S x
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p 1 S y
  rw [← map_add, WittVector.coeff_truncate, WittVector.coeff_truncate, WittVector.coeff_truncate]
  exact WittVector.add_coeff_zero x y

theorem coordinate_mem_wittHom :
    TruncatedWittVector.mk p (fun _ : Fin 1 => coordinate R) ∈ wittHom R p 1 (Ga R) := by
  rw [mem_wittHom_iff]
  refine TruncatedWittVector.ext fun i => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rw [coeff_zero_add_of_length_one, TruncWitt.coeff_map, TruncWitt.coeff_map,
    TruncWitt.coeff_map, TruncatedWittVector.coeff_mk]
  change Coalgebra.comul (R := R) (coordinate R) = _
  rw [coordinate, SymmetricAlgebra.comul_ι]
  rfl

theorem of_coordinate_ne_zero [Nontrivial R] :
    DieudonneModule.of R p (Ga R) 1
      ⟨TruncatedWittVector.mk p (fun _ : Fin 1 => coordinate R), coordinate_mem_wittHom R p⟩ ≠ 0 := by
  intro h
  have h1 := DieudonneModule.of_injective 1 (h.trans (map_zero _).symm)
  have h2 := congrArg (fun x : wittHom R p 1 (Ga R) => (x : TruncatedWittVector p 1 (Ga R)).coeff 0) h1
  simp only [TruncatedWittVector.coeff_mk, AddSubgroup.coe_zero,
    TruncatedWittVector.coeff_zero] at h2
  exact coordinate_ne_zero R h2

end DieudonneModule.Examples

end Deformation


