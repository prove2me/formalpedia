-- Prove2me | Definitions.Def_IharaMennickeCarrier
-- name    : IharaMennickeCarrier
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/f9a6bb7c-13f9-5235-96ec-5a9e8856fda6
-- title:
--   Mennicke's generators and subgroups for SL2​(Z[1/q])
-- statement:
--   Throughout, $q$ is a natural number and `ZAway q` denotes the localisation of $\mathbb{Z}$ away from $q$, i.e. $\mathbb{Z}[1/q]$; the ambient group is $G = SL_2(\mathbb{Z}[1/q])$. The module fixes the vocabulary for Mennicke's analysis of this group. First, [`Ihara.mennickeA`](../def/IharaMennickeCarrier.html#L14) is the element $A = \begin{pmatrix}1&0\\1&1\end{pmatrix}$ of $SL_2(\mathbb{Z})$, with [`Ihara.mennickeA_pow_coe`](../def/IharaMennickeCarrier.html#L21) computing $A^k$ as the lower unipotent matrix with entry $k$. For $N$ coprime to $q$, [`Ihara.slAwayReduction`](../def/IharaMennickeCarrier.html#L35) is the entrywise reduction $G \to SL_2(\mathbb{Z}/N)$ induced by the ring map $\mathbb{Z}[1/q] \to \mathbb{Z}/N$ of [`Ihara.zAwayToZMod`](../def/Gamma0AwayUnitsChar.html#L19), and [`Ihara.principalCongruenceAway`](../def/IharaMennickeCarrier.html#L42) is its kernel $N_N$, a normal subgroup of $G$; [`Ihara.slToAway_mennickeA_pow_mem`](../def/IharaMennickeCarrier.html#L56) shows that the image of $A^N$ in $G$ lies in $N_N$. The predicate [`Ihara.MennickeCSP`](../def/IharaMennickeCarrier.html#L52) asserts the equality $N_N = Q_N$, where $Q_N$ is the normal closure in $G$ of the single element $A^N$; the inclusion $Q_N \le N_N$ is established, and [`Ihara.mennickeCSP_iff_ker_le`](../def/IharaMennickeCarrier.html#L72) restates the predicate as the reverse inclusion. Next, [`Ihara.qInv`](../def/IharaMennickeCarrier.html#L88) is the inverse of $q$ in $\mathbb{Z}[1/q]$ and [`Ihara.mennickeU`](../def/IharaMennickeCarrier.html#L96) the diagonal element $U = \mathrm{diag}(q, q^{-1})$ of $G$. Writing $Q_m$ ([`Ihara.mennickeQ`](../def/IharaMennickeCarrier.html#L115)) for the normal closure of $A^m$, the subgroup [`Ihara.mennickeZ`](../def/IharaMennickeCarrier.html#L118) is the preimage under $G \to G/Q_m$ of the centraliser of the image of $N_m$; equivalently, $g \in Z_m$ iff $[g, X] \in Q_m$ for every $X \in N_m$, and $Q_m \le Z_m$. Finally four $\mathrm{Prop}$-valued definitions record statements to be proved elsewhere: [`Ihara.MennickeSaturated`](../def/IharaMennickeCarrier.html#L161) ($(q^2-1) \mid m$, with natural subtraction, and every prime divisor of $m$ divides $q^2-1$); [`Ihara.MennickeCentralityCoprime`](../def/IharaMennickeCarrier.html#L164) (if $m$ is coprime to $q^2-1$ then $Z_m = G$); [`Ihara.MennickeLemma22Statement`](../def/IharaMennickeCarrier.html#L167) ($Z_m = G$ for every $m$ coprime to $q$ that is saturated in the above sense); and [`Ihara.MennickeLemma21`](../def/IharaMennickeCarrier.html#L176) ($U \in Z_m$).
--
--   **Relation to Mathlib.** Built from Mathlib's `Localization.Away`, `Matrix.SpecialLinearGroup.map`, `Subgroup.normalClosure` and `Subgroup.centralizer`; Mathlib's congruence subgroups are defined only inside $SL_2(\mathbb{Z})$, so the principal congruence subgroups of $SL_2(\mathbb{Z}[1/q])$ and Mennicke's subgroups $Q_m$, $Z_m$ are the project's own.
--
--   **Where it is used.** These notions support the study of $SL_2(\mathbb{Z}[1/q])$ and of the homomorphism from the amalgam of two copies of $\Gamma_0(N)$ along $\Gamma_0(Nq)$ into it, which is the group-theoretic input to Ihara's lemma in the level-raising part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_IharaMennickeCarrier.lean

import Definitions.Def_Gamma0Away
import Definitions.Def_IharaAmalgamMap
import Definitions.Def_Gamma0AwayUnitsChar
import Mathlib.GroupTheory.Subgroup.Simple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Matrix

open scoped MatrixGroups

namespace Ihara

section MennickeGenerator

def mennickeA : SL(2, ℤ) :=
  ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[simp]
theorem mennickeA_coe :
    ((mennickeA : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 1, 1] := rfl

theorem mennickeA_pow_coe (k : ℕ) :
    ((mennickeA ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; (k : ℤ), 1] := by
  induction k with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, mennickeA_coe, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp

end MennickeGenerator

section Carrier

variable (N q : ℕ)

noncomputable def slAwayReduction (hNq : Nat.Coprime N q) : SL(2, ZAway q) →* SL(2, ZMod N) :=
  Matrix.SpecialLinearGroup.map (zAwayToZMod N q hNq)

theorem slAwayReduction_coe (hNq : Nat.Coprime N q) (g : SL(2, ZAway q)) :
    ((slAwayReduction N q hNq g : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      (g : Matrix (Fin 2) (Fin 2) (ZAway q)).map (zAwayToZMod N q hNq) := rfl

noncomputable def principalCongruenceAway (hNq : Nat.Coprime N q) :
    Subgroup SL(2, ZAway q) :=
  (slAwayReduction N q hNq).ker

instance (hNq : Nat.Coprime N q) : (principalCongruenceAway N q hNq).Normal :=
  MonoidHom.normal_ker (slAwayReduction N q hNq)

theorem mem_principalCongruenceAway_iff (hNq : Nat.Coprime N q) {g : SL(2, ZAway q)} :
    g ∈ principalCongruenceAway N q hNq ↔ slAwayReduction N q hNq g = 1 := Iff.rfl

def MennickeCSP (hNq : Nat.Coprime N q) : Prop :=
  principalCongruenceAway N q hNq =
    Subgroup.normalClosure ({(slToAway q mennickeA) ^ N} : Set SL(2, ZAway q))

theorem slToAway_mennickeA_pow_mem (hNq : Nat.Coprime N q) :
    (slToAway q mennickeA) ^ N ∈ principalCongruenceAway N q hNq := by
  rw [mem_principalCongruenceAway_iff, ← map_pow]
  apply Subtype.ext
  rw [slAwayReduction_coe, coe_slToAway, mennickeA_pow_coe, Matrix.map_map,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Function.comp_apply]

theorem normalClosure_le_principalCongruenceAway (hNq : Nat.Coprime N q) :
    Subgroup.normalClosure ({(slToAway q mennickeA) ^ N} : Set SL(2, ZAway q)) ≤
      principalCongruenceAway N q hNq :=
  Subgroup.normalClosure_le_normal
    (Set.singleton_subset_iff.mpr (slToAway_mennickeA_pow_mem N q hNq))

theorem mennickeCSP_iff_ker_le (hNq : Nat.Coprime N q) :
    MennickeCSP N q hNq ↔
      principalCongruenceAway N q hNq ≤
        Subgroup.normalClosure ({(slToAway q mennickeA) ^ N} : Set SL(2, ZAway q)) := by
  constructor
  · intro h; rw [h]
  · intro h; exact le_antisymm h (normalClosure_le_principalCongruenceAway N q hNq)

end Carrier

section DiagonalGenerator

noncomputable section

variable (q : ℕ)

def qInv : ZAway q := IsLocalization.Away.invSelf (S := ZAway q) ((q : ℕ) : ℤ)

theorem natCast_q_mul_qInv : ((q : ℕ) : ZAway q) * qInv q = 1 :=
  q_mul_invSelf q

theorem qInv_mul_natCast_q : qInv q * ((q : ℕ) : ZAway q) = 1 :=
  invSelf_mul_q q

def mennickeU : SL(2, ZAway q) :=
  ⟨!![((q : ℕ) : ZAway q), 0; 0, qInv q], by
    rw [Matrix.det_fin_two_of, natCast_q_mul_qInv q]; ring⟩

@[simp]
theorem mennickeU_coe :
    ((mennickeU q : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![((q : ℕ) : ZAway q), 0; 0, qInv q] := rfl

end

end DiagonalGenerator

open scoped MatrixGroups commutatorElement

section Carrier

variable (q m : ℕ)

noncomputable abbrev mennickeQ : Subgroup SL(2, ZAway q) :=
  Subgroup.normalClosure ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))

noncomputable def mennickeZ (hmq : Nat.Coprime m q) : Subgroup SL(2, ZAway q) :=
  Subgroup.comap
    (QuotientGroup.mk' (mennickeQ q m))
    (Subgroup.centralizer
      (Subgroup.map (QuotientGroup.mk' (mennickeQ q m))
        (principalCongruenceAway m q hmq)))

theorem mem_mennickeZ_iff (hmq : Nat.Coprime m q) (g : SL(2, ZAway q)) :
    g ∈ mennickeZ q m hmq ↔
      ∀ X ∈ principalCongruenceAway m q hmq, ⁅g, X⁆ ∈ mennickeQ q m := by
  constructor
  · intro hg X hX
    rw [mennickeZ, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hg
    have hcomm := hg (QuotientGroup.mk' _ X) (Subgroup.mem_map_of_mem _ hX)
    rw [← QuotientGroup.ker_mk' (mennickeQ q m), MonoidHom.mem_ker,
      map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  · intro h
    rw [mennickeZ, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_map] at hy
    obtain ⟨X, hX, rfl⟩ := hy
    have hc := h X hX
    rw [← QuotientGroup.ker_mk' (mennickeQ q m), MonoidHom.mem_ker,
      map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc.symm

theorem mennickeQ_le_mennickeZ (hmq : Nat.Coprime m q) :
    mennickeQ q m ≤ mennickeZ q m hmq := by
  intro x hx
  rw [mennickeZ, Subgroup.mem_comap]
  have hx1 : QuotientGroup.mk' (mennickeQ q m) x = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hx
  rw [hx1]
  exact Subgroup.one_mem _

end Carrier

section Regimes

variable (q m : ℕ)

def MennickeSaturated : Prop :=
  (q ^ 2 - 1) ∣ m ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)

def MennickeCentralityCoprime (hmq : Nat.Coprime m q) : Prop :=
  Nat.Coprime m (q ^ 2 - 1) → mennickeZ q m hmq = ⊤

def MennickeLemma22Statement : Prop :=
  ∀ m : ℕ, ∀ hmq : Nat.Coprime m q, MennickeSaturated q m → mennickeZ q m hmq = ⊤

end Regimes

section Lemma21

variable (q m : ℕ) [NeZero q]

def MennickeLemma21 (hmq : Nat.Coprime m q) : Prop :=
  mennickeU q ∈ mennickeZ q m hmq

omit [NeZero q] in

theorem mennickeLemma21_iff (hmq : Nat.Coprime m q) :
    MennickeLemma21 q m hmq ↔ mennickeU q ∈ mennickeZ q m hmq :=
  Iff.rfl

end Lemma21

end Ihara


