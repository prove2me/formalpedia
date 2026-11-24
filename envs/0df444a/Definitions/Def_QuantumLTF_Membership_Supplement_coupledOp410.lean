-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_coupledOp410
-- name    : QuantumLTF_Membership_Supplement_coupledOp410
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-24T06:01:18.444414+00:00
-- url     : https://prove2.me/theorems/c815e4c1-8314-414a-b388-8d80270537f9
-- title:
--   Coupled Transducer Operators and Catalyst States for Bounded-Size Majority Learning
-- statement:
--   This defines the explicit block unitaries, coupled adversary polynomials, catalyst vectors, and odd-cardinality parity-lift operators underlying the gate- and depth-efficient quantum learning algorithm for $\mathrm{MAJORITY}_A$ under the bounded-size promise $1 \le |A| \le k$ (Krivcenko, Nguyen, de Wolf 2026, Section 4.3, Section 4.5.3, and Appendix C.5.2).
--
--   Let $n \ge 1$ be the number of input variables, $M = \lfloor k/2 \rfloor$ be the maximum layer index, and $q_W = \lceil \log_2(M+2) \rceil$ be the mode-register width encoding the $(M+2)$-dimensional direct-sum space $\mathbb{C} \oplus W$, where $\mathbb{C} = \mathrm{span}\{\lvert V\rangle\}$ corresponds to label $0$ and $W = \mathrm{span}\{\lvert e_*\rangle, \lvert e_0\rangle, \dots, \lvert e_{M-1}\rangle\}$ corresponds to labels $1, 2, \dots, M+1$. Let $n' = n+1$.
--
--   1. **Odd-cardinality parity lift:** Given $A \subseteq [n]$ with $1 \le |A| \le k$, define $\operatorname{liftOdd}(A) \subseteq [n+1]$ by keeping $A$ unchanged when $|A|$ is odd and adjoining the parity coordinate $n$ when $|A|$ is even, so $|\operatorname{liftOdd}(A)| = 2m + 1$ for an integer layer $m = \operatorname{layerOf}(A) \le M$.
--   2. **Coupled adversary polynomials:** For $0 \le l \le M$, $P_l(X)$ and $Q_l(X)$ are the normalized mod-4 polynomials with $P_l(0) = Q_l(0) = 1/\sqrt{2}$, and for $m < l$, $C_{m,l}(X) = X D_{m,l}(X)$ removes the $(2m+2)$-root from $Q_l$ (if $m$ is even) or $P_l$ (if $m$ is odd). The $W$-valued polynomials $\vec{p}_l, \vec{q}_l$ determine the input/output catalyst coefficients $\vec{a}_m(t) = ((-1)^t \vec{q}_m(t) - \vec{p}_m(t))/\sqrt{2}$ and $\vec{b}_m(t) = (\vec{p}_m(t) + (-1)^t \vec{q}_m(t))/\sqrt{2}$.
--   3. **Explicit block factorization $U_t = R_t (I_{\mathbb{C}} \oplus D_t)$:** For $0 \le t \le 2M+1$, `D_mat410 M t` implements the diagonal parity/comparison reflection (`(-1)^{i+1}` on $e_i$ for $t=0$; `(-1)^{\lfloor t/2 \rfloor}` on $e_*$ and `(-1)^{\min(i, \lfloor t/2 \rfloor)}` on $e_i$ for $t \ge 1$), while `R_mat410 M t` implements the $\lvert V\rangle \leftrightarrow \lvert e_*\rangle$ swap at $t=0$, the conjugate plane rotation $H_{*,j} R_{0,1}(\rho_j) H_{*,j}$ at odd interior $t = 2j+1 < 2M+1$, and the boundary rotation on $\mathrm{span}\{\lvert V\rangle, \lvert e_*\rangle\}$ at $t = 2M+1$. For $t > 2M+1$, `U_op410 M t = I`.
--   4. **Two-register transducer and catalyst:** `H_hat410` applies $H^{\otimes n'}$ to the $n'$-qubit register iff the mode register lies in $W$; `U_tilde410` applies $\sum_q \lvert q\rangle\langle q\rvert \otimes U_{|q|}$; `U_ideal410 = H_hat410 * U_tilde410 * H_hat410`. The catalyst vectors `wCatVec410` and `wCatAfter410` (with coefficients in `Krawtchouk` weight basis for $\vec{b}_m$ and $\vec{a}_m$) are intertwined by `phaseCtrl410`, the controlled Majority phase oracle $I \oplus O_B^{\pm}$.
--
--   **Formalization Note.** Mode labels `0, ..., M+1` are encoded in least-significant-bit order via `modeKet M idx = natToBitsLSB (qW M) idx` (`qW M = Nat.clog 2 (M + 2)`). The file also includes the elementary LSB injectivity and bijectivity lemmas required to certify distinctness of the two-level basis labels inside `R_mat410`.
-- source:
--   Krivcenko, Nguyen, de Wolf (2026), Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Section 4.3, Eq. (118)-(127) (pp. 45-50), Section 4.5.3, Eq. (144)-(148) (pp. 55-57), and Appendix C.5.2 (pp. 96-99).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement.CoupledOp410

open QAlgorithms QuantumLTF.Majority

/-- Lifts a subset `A ⊆ Fin n` with `1 ≤ |A| ≤ k` to an odd-cardinality subset of `Fin (n + 1)`
by adjoining the parity qubit `Fin.last n` iff `|A|` is even (Appendix C.5.3 / Eq. (127)). -/
def liftOdd {n k : ℕ} (A : BoundedSupports n k) : Finset (Fin (n + 1)) :=
  if Odd A.1.card then A.1.map Fin.castSuccEmb
  else insert (Fin.last n) (A.1.map Fin.castSuccEmb)

/-- Layer index `m` such that `|liftOdd A| = 2 * m + 1`. -/
def layerOf {n k : ℕ} (A : BoundedSupports n k) : ℕ :=
  ((liftOdd A).card - 1) / 2

/-- Least-significant-bit binary encoding of `val` into `ℓ` qubits. -/
def natToBitsLSB (ℓ val : ℕ) : Qubits ℓ := fun j => val.testBit j.val

/-- Decoding of an `ℓ`-qubit LSB basis state `v` to a natural number `< 2 ^ ℓ`. -/
def bitsToNatLSB {ℓ : ℕ} (v : Qubits ℓ) : ℕ :=
  ∑ j : Fin ℓ, if v j then 2 ^ j.val else 0

lemma bitsToNatLSB_lt (ℓ : ℕ) (v : Qubits ℓ) : bitsToNatLSB v < 2 ^ ℓ := by
  induction ℓ with
  | zero => simp [bitsToNatLSB]
  | succ ℓ ih =>
    simp only [bitsToNatLSB, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    have hinit : (∑ i : Fin ℓ, if v i.castSucc then 2 ^ i.val else 0) < 2 ^ ℓ :=
      ih (fun i => v i.castSucc)
    have hlast : (if v (Fin.last ℓ) then 2 ^ ℓ else 0) ≤ 2 ^ ℓ := by split_ifs <;> omega
    rw [pow_succ']
    omega

lemma natToBitsLSB_zero (ℓ : ℕ) : natToBitsLSB ℓ 0 = fun _ => false := by
  funext j
  simp [natToBitsLSB]

lemma bitsToNatLSB_natToBitsLSB {ℓ val : ℕ} (h : val < 2 ^ ℓ) :
    bitsToNatLSB (natToBitsLSB ℓ val) = val := by
  induction ℓ generalizing val with
  | zero =>
    simp only [pow_zero] at h
    have : val = 0 := by omega
    subst this
    simp [bitsToNatLSB]
  | succ ℓ ih =>
    simp only [bitsToNatLSB, natToBitsLSB, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    have hmod_lt : val % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt val (Nat.two_pow_pos ℓ)
    have hih := ih hmod_lt
    have hleft : (∑ i : Fin ℓ, if natToBitsLSB (ℓ + 1) val i.castSucc then 2 ^ i.val else 0) = val % 2 ^ ℓ := by
      rw [← hih]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : i.val < ℓ := i.isLt
      have htb : val.testBit i.val = (val % 2 ^ ℓ).testBit i.val := by
        rw [Nat.testBit_mod_two_pow]
        simp [hi]
      simp only [natToBitsLSB, Fin.val_castSucc]
      by_cases hc : val.testBit i.val <;> simp [hc, htb.symm]
    change (∑ i : Fin ℓ, if natToBitsLSB (ℓ + 1) val i.castSucc then 2 ^ i.val else 0) +
      (if val.testBit ℓ then 2 ^ ℓ else 0) = val
    rw [hleft]
    have hdiv_lt : val / 2 ^ ℓ < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos ℓ)]
      simpa [pow_succ'] using h
    have hbit : val.testBit ℓ = decide (val / 2 ^ ℓ = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have : (val / 2 ^ ℓ) % 2 = val / 2 ^ ℓ := Nat.mod_eq_of_lt hdiv_lt
      rw [this]
    rw [hbit]
    have hdecomp := (Nat.div_add_mod val (2 ^ ℓ)).symm
    by_cases h0 : val / 2 ^ ℓ = 0
    · simp only [h0, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte, add_zero]
      rw [h0, mul_zero, zero_add] at hdecomp
      exact hdecomp.symm
    · have h1 : val / 2 ^ ℓ = 1 :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp hdiv_lt) (Nat.pos_of_ne_zero h0)
      simp only [h1, decide_true, ↓reduceIte]
      rw [h1, mul_one] at hdecomp
      linarith [hdecomp]

lemma natToBitsLSB_inj {ℓ a b : ℕ} (ha : a < 2 ^ ℓ) (hb : b < 2 ^ ℓ)
    (h : natToBitsLSB ℓ a = natToBitsLSB ℓ b) : a = b := by
  have := congrArg bitsToNatLSB h
  rwa [bitsToNatLSB_natToBitsLSB ha, bitsToNatLSB_natToBitsLSB hb] at this

/-- Number of mode qubits representing `C ⊕ W` where `W = span{e_*, e_0, ..., e_{M-1}}`. -/
def qW (M : ℕ) : ℕ := Nat.clog 2 (M + 2)

lemma lt_two_pow_qW (M : ℕ) : M + 2 ≤ 2 ^ qW M :=
  Nat.le_pow_clog (by norm_num) (M + 2)

lemma one_le_qW (M : ℕ) : 1 ≤ qW M := by
  have h1 : 2 ≤ 2 ^ qW M := by have := lt_two_pow_qW M; omega
  by_contra h0
  have hq : qW M = 0 := by omega
  rw [hq] at h1
  omega

lemma two_le_qW {M : ℕ} (hM : 1 ≤ M) : 2 ≤ qW M := by
  have h1 : 3 ≤ 2 ^ qW M := by have := lt_two_pow_qW M; omega
  by_contra hlt
  have hle : qW M ≤ 1 := by omega
  have hpow : 2 ^ qW M ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
  omega

/-- Computational-basis encoding of mode label `idx ∈ {0, 1, ..., M + 1}` in `Qubits (qW M)`. -/
def modeKet (M idx : ℕ) : Qubits (qW M) := natToBitsLSB (qW M) idx

lemma modeKet_zero (M : ℕ) : modeKet M 0 = fun _ => false :=
  natToBitsLSB_zero (qW M)

lemma modeKet_ne (M a b : ℕ) (ha : a < M + 2) (hb : b < M + 2) (hne : a ≠ b) :
    modeKet M a ≠ modeKet M b := by
  intro h
  apply hne
  exact natToBitsLSB_inj (lt_of_lt_of_le ha (lt_two_pow_qW M))
    (lt_of_lt_of_le hb (lt_two_pow_qW M)) h

lemma bitsToNatLSB_modeKet (M idx : ℕ) (hidx : idx < M + 2) :
    bitsToNatLSB (modeKet M idx) = idx :=
  bitsToNatLSB_natToBitsLSB (lt_of_lt_of_le hidx (lt_two_pow_qW M))

lemma modeKet_injOn (M : ℕ) :
    Function.Injective (fun c : Fin (M + 1) => modeKet M (c.1 + 1)) := by
  intro c₁ c₂ h
  ext
  have heq := congrArg bitsToNatLSB h
  rw [bitsToNatLSB_modeKet M (c₁.1 + 1) (by omega),
    bitsToNatLSB_modeKet M (c₂.1 + 1) (by omega)] at heq
  omega

/-- Root set of the even-channel adversary polynomial `p_m`. -/
def rootSetP (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * m)).filter fun r => r % 4 = 0 ∨ r % 4 = 1

/-- Root set of the odd-channel adversary polynomial `q_m`. -/
def rootSetQ (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * m)).filter fun r => r % 4 = 2 ∨ r % 4 = 3

/-- Unnormalized polynomial with root set `rootSetP m`. -/
noncomputable def pPolyRaw (m : ℕ) : Polynomial ℝ :=
  ∏ r ∈ rootSetP m, (Polynomial.X - Polynomial.C (r : ℝ))

/-- Unnormalized polynomial with root set `rootSetQ m`. -/
noncomputable def qPolyRaw (m : ℕ) : Polynomial ℝ :=
  ∏ r ∈ rootSetQ m, (Polynomial.X - Polynomial.C (r : ℝ))

/-- Normalized polynomial `p_m(X)` with `p_m(0) = 1 / √2` (Lemma 4.5). -/
noncomputable def PPoly (m : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / (Real.sqrt 2 * (pPolyRaw m).eval 0)) * pPolyRaw m

/-- Normalized polynomial `q_m(X)` with `q_m(0) = 1 / √2` (Lemma 4.5). -/
noncomputable def QPoly (m : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / (Real.sqrt 2 * (qPolyRaw m).eval 0)) * qPolyRaw m

/-- Divided-difference polynomial eliminating the `(2m + 2)` root. -/
noncomputable def DPoly (m l : ℕ) : Polynomial ℝ :=
  if Even m then
    Polynomial.C (1 / (Real.sqrt 2 * (qPolyRaw l).eval 0)) *
      ∏ r ∈ (rootSetQ l).erase (2 * m + 2), (Polynomial.X - Polynomial.C (r : ℝ))
  else
    Polynomial.C (1 / (Real.sqrt 2 * (pPolyRaw l).eval 0)) *
      ∏ r ∈ (rootSetP l).erase (2 * m + 2), (Polynomial.X - Polynomial.C (r : ℝ))

/-- Coupling polynomial `C_{m,l}(X) = X · D_{m,l}(X)`. -/
noncomputable def CPoly (m l : ℕ) : Polynomial ℝ :=
  Polynomial.X * DPoly m l

/-- Mode-vector polynomial `p⃗_l(X)` in `ℝ^{M+1}` (Lemma 4.5 / Appendix C.5.2). -/
noncomputable def pVecPoly (M l : ℕ) (c : Fin (M + 1)) : Polynomial ℝ :=
  Fin.cases (PPoly l) (fun j : Fin M =>
    if (j : ℕ) < l ∧ ¬ Even (j : ℕ) then
      Polynomial.C (1 / ((2 * (j : ℕ) + 1 : ℕ) : ℝ)) * CPoly j l
    else if (j : ℕ) = l ∧ Even (j : ℕ) then
      PPoly l
    else 0) c

/-- Mode-vector polynomial `q⃗_l(X)` in `ℝ^{M+1}` (Lemma 4.5 / Appendix C.5.2). -/
noncomputable def qVecPoly (M l : ℕ) (c : Fin (M + 1)) : Polynomial ℝ :=
  Fin.cases (QPoly l) (fun j : Fin M =>
    if (j : ℕ) < l ∧ Even (j : ℕ) then
      Polynomial.C (1 / ((2 * (j : ℕ) + 1 : ℕ) : ℝ)) * CPoly j l
    else if (j : ℕ) = l ∧ ¬ Even (j : ℕ) then
      QPoly l
    else 0) c

/-- Two-level matrix acting as `M2` on `span{|u⟩, |v⟩}` and as identity elsewhere. -/
noncomputable def twoLevelMat {ι : Type*} [DecidableEq ι] (u v : ι) (_huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun r c =>
    if r = u ∧ c = u then M2 false false
    else if r = u ∧ c = v then M2 false true
    else if r = v ∧ c = u then M2 true false
    else if r = v ∧ c = v then M2 true true
    else if r ≠ u ∧ r ≠ v ∧ c = r then 1
    else 0

/-- Diagonal sign function of the unitary `D_t` in the factorization `U_t = R_t D_t` (Appendix C.5.2). -/
def diagSign410 (M t : ℕ) (v : Qubits (qW M)) : ℂ :=
  let s := bitsToNatLSB v
  if t = 0 then
    if s ≤ 1 then 1 else (-1 : ℂ) ^ (s + 1)
  else
    let h := t / 2
    if s = 0 then 1
    else if s = 1 then (-1 : ℂ) ^ h
    else (-1 : ℂ) ^ (min (s - 2) h)

/-- Diagonal reflection factor `D_t` on `C ⊕ W`. -/
noncomputable def D_mat410 (M t : ℕ) : Matrix (Qubits (qW M)) (Qubits (qW M)) ℂ :=
  Matrix.diagonal (diagSign410 M t)

/-- Ratio `ρ_j` used to construct the interior two-level rotation `R_{2j}` (Appendix C.5.2). -/
noncomputable def rhoJ (j : ℕ) : ℝ :=
  if Even j then 2 * (PPoly j).eval ((2 * j + 1 : ℕ) : ℝ)
  else -2 * (QPoly j).eval ((2 * j + 1 : ℕ) : ℝ)

/-- Parameter `A_j = -(ρ_j + ρ_j^{-1}) / 2`. -/
noncomputable def AJ (j : ℕ) : ℝ := -(rhoJ j + (rhoJ j)⁻¹) / 2

/-- Parameter `B_j = (ρ_j - ρ_j^{-1}) / 2`. -/
noncomputable def BJ (j : ℕ) : ℝ := (rhoJ j - (rhoJ j)⁻¹) / 2

/-- 2×2 orthogonal rotation matrix acting on `span{|V⟩, (|e_*⟩ + |e_j⟩)/√2}`. -/
noncomputable def R2J (j : ℕ) : Matrix Bool Bool ℂ :=
  Matrix.of fun r c =>
    match r, c with
    | false, false => (BJ j / AJ j : ℂ)
    | false, true  => (1 / AJ j : ℂ)
    | true, false  => (-1 / AJ j : ℂ)
    | true, true   => (BJ j / AJ j : ℂ)

/-- Boundary normalization factor `α_M` for `t = 2M + 1`. -/
noncomputable def alphaM (M : ℕ) : ℝ :=
  (-1 : ℝ) ^ (M + 1) * ((PPoly M).eval ((2 * M + 1 : ℕ) : ℝ) + (QPoly M).eval ((2 * M + 1 : ℕ) : ℝ)) / Real.sqrt 2

/-- Boundary rotation numerator `β_M` for `t = 2M + 1`. -/
noncomputable def betaM (M : ℕ) : ℝ :=
  ((PPoly M).eval ((2 * M + 1 : ℕ) : ℝ) - (QPoly M).eval ((2 * M + 1 : ℕ) : ℝ)) / Real.sqrt 2

/-- 2×2 boundary orthogonal rotation matrix between `|V⟩` and `|e_*⟩` at `t = 2M + 1`. -/
noncomputable def R2Top (M : ℕ) : Matrix Bool Bool ℂ :=
  Matrix.of fun r c =>
    match r, c with
    | false, false => (betaM M / alphaM M : ℂ)
    | false, true  => (1 / alphaM M : ℂ)
    | true, false  => (-1 / alphaM M : ℂ)
    | true, true   => (betaM M / alphaM M : ℂ)

/-- Rotation factor `R_t` of Appendix C.5.2. -/
noncomputable def R_mat410 (M t : ℕ) : Matrix (Qubits (qW M)) (Qubits (qW M)) ℂ :=
  if t = 0 then
    twoLevelMat (modeKet M 0) (modeKet M 1) (modeKet_ne M 0 1 (by omega) (by omega) (by omega)) pauliX
  else if h : Odd t ∧ t / 2 < M then
    let j := t / 2
    have hj : 2 + j < M + 2 := by omega
    let H12 := twoLevelMat (modeKet M 1) (modeKet M (2 + j))
      (modeKet_ne M 1 (2 + j) (by omega) hj (by omega)) hadamard
    let R01 := twoLevelMat (modeKet M 0) (modeKet M 1)
      (modeKet_ne M 0 1 (by omega) (by omega) (by omega)) (R2J j)
    H12 * R01 * H12
  else if 1 ≤ M ∧ t = 2 * M + 1 then
    twoLevelMat (modeKet M 0) (modeKet M 1)
      (modeKet_ne M 0 1 (by omega) (by omega) (by omega)) (R2Top M)
  else 1

/-- Coupled transducer step unitary `U_t = R_t D_t` on `qW M` mode qubits (Appendix C.5.2). -/
noncomputable def U_op410 (M t : ℕ) : Matrix (Qubits (qW M)) (Qubits (qW M)) ℂ :=
  if 2 * M + 1 < t then 1 else R_mat410 M t * D_mat410 M t

/-- Transducer input catalyst coordinate vector `a⃗_m(t)`. -/
noncomputable def aVec (M m : ℕ) (t : Fin (2 * m + 2)) (c : Fin (M + 1)) : ℝ :=
  ((-1 : ℝ) ^ t.1 * (qVecPoly M m c).eval (t.1 : ℝ) - (pVecPoly M m c).eval (t.1 : ℝ)) / Real.sqrt 2

/-- Transducer output catalyst coordinate vector `b⃗_m(t)`. -/
noncomputable def bVec (M m : ℕ) (t : Fin (2 * m + 2)) (c : Fin (M + 1)) : ℝ :=
  ((pVecPoly M m c).eval (t.1 : ℝ) + (-1 : ℝ) ^ t.1 * (qVecPoly M m c).eval (t.1 : ℝ)) / Real.sqrt 2

/-- Controlled Hadamard transform `Ĥ` applying `H^{⊗ n'}` iff the mode register is in `W` (`≠ modeKet M 0`). -/
noncomputable def H_hat410 (M n' : ℕ) :
    Matrix (Qubits (qW M) × Qubits n') (Qubits (qW M) × Qubits n') ℂ :=
  Matrix.of fun (m₁, q₁) (m₂, q₂) =>
    if m₁ = m₂ then
      if m₁ = modeKet M 0 then (1 : Matrix (Qubits n') (Qubits n') ℂ) q₁ q₂
      else hadamardN n' q₁ q₂
    else 0

/-- Hamming-weight multiplexed unitary `Ũ = ∑_q U_{|q|} ⊗ |q⟩⟨q|` on `mode × Q_ext`. -/
noncomputable def U_tilde410 (M n' : ℕ) :
    Matrix (Qubits (qW M) × Qubits n') (Qubits (qW M) × Qubits n') ℂ :=
  Matrix.of fun (m₁, q₁) (m₂, q₂) =>
    if q₁ = q₂ then U_op410 M (hammingWeight q₁) m₁ m₂ else 0

/-- Ideal conjugated transducer step `U_ideal = Ĥ Ũ Ĥ` acting on `mode × Q_ext`. -/
noncomputable def U_ideal410 (M n' : ℕ) :
    Matrix (Qubits (qW M) × Qubits n') (Qubits (qW M) × Qubits n') ℂ :=
  H_hat410 M n' * U_tilde410 M n' * H_hat410 M n'

/-- Coordinate `c` of the catalyst state `|w⟩` before the phase query. -/
noncomputable def wCatCoord410 (n' M m : ℕ) (B : Finset (Fin n')) (hB : B.card = 2 * m + 1)
    (c : Fin (M + 1)) : EuclideanSpace ℂ (Qubits n') :=
  WithLp.toLp 2 fun S : Qubits n' =>
    (((Real.sqrt 2)⁻¹ ^ n' : ℝ) : ℂ) *
      ∑ t : Fin (2 * m + 2),
        (krawtchouk (2 * m + 1) t (intersectionIndex ⟨B, hB⟩ S) : ℂ) * (bVec M m t c : ℂ)

/-- Coordinate `c` of the catalyst state `|w'⟩` after the phase query. -/
noncomputable def wCatAfterCoord410 (n' M m : ℕ) (B : Finset (Fin n')) (hB : B.card = 2 * m + 1)
    (c : Fin (M + 1)) : EuclideanSpace ℂ (Qubits n') :=
  WithLp.toLp 2 fun S : Qubits n' =>
    (((Real.sqrt 2)⁻¹ ^ n' : ℝ) : ℂ) *
      ∑ t : Fin (2 * m + 2),
        (krawtchouk (2 * m + 1) t (intersectionIndex ⟨B, hB⟩ S) : ℂ) * (aVec M m t c : ℂ)

/-- Pre-query catalyst vector `|w⟩` on `mode × Q_ext` supported exclusively on `W` (`modeKet M 1..M+1`). -/
noncomputable def wCatVec410 (n' M m : ℕ) (B : Finset (Fin n')) (hB : B.card = 2 * m + 1) :
    EuclideanSpace ℂ (Qubits (qW M) × Qubits n') :=
  ∑ c : Fin (M + 1), tensorVec (ket (modeKet M (c.1 + 1))) (wCatCoord410 n' M m B hB c)

/-- Post-query catalyst vector `|w'⟩` on `mode × Q_ext`. -/
noncomputable def wCatAfter410 (n' M m : ℕ) (B : Finset (Fin n')) (hB : B.card = 2 * m + 1) :
    EuclideanSpace ℂ (Qubits (qW M) × Qubits n') :=
  ∑ c : Fin (M + 1), tensorVec (ket (modeKet M (c.1 + 1))) (wCatAfterCoord410 n' M m B hB c)

/-- Controlled Majority phase query `I ⊕ O^±_B` acting on `W` (`mode ≠ modeKet M 0`). -/
noncomputable def phaseCtrl410 (M n' : ℕ) (B : Finset (Fin n')) :
    Matrix (Qubits (qW M) × Qubits n') (Qubits (qW M) × Qubits n') ℂ :=
  Matrix.of fun (m₁, q₁) (m₂, q₂) =>
    if m₁ = m₂ ∧ q₁ = q₂ then
      if m₁ ≠ modeKet M 0 ∧ majorityBit B q₁ then (-1 : ℂ) else 1
    else 0

end QuantumLTF.Membership.Supplement.CoupledOp410


