-- Prove2me | Definitions.Def_NoisyOWMPC_accessHalf
-- name    : NoisyOWMPC_accessHalf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:49:47.533652+00:00
-- url     : https://prove2.me/theorems/4fa1bc95-2bd6-4adf-b196-d28537fe3d61
-- title:
--   The access test of Construction 5.6 (protocol half)
-- statement:
--   For a word $x\in\mathcal X^L$, a query $y\in\mathcal Y_i^L$ and $(a,b)\in\mathcal X\times\mathcal Y_i$ put $N_a(x)=|\{s:x_s=a\}|$, $N_{a,b}(x,y)=|\{s:x_s=a,y_s=b\}|$ and $\mathrm{Ratio}_{a\to b}(x,y)=N_{a,b}(x,y)/N_a(x)$ (or $0$ if $N_a(x)=0$). The **global predicate** (5.9) is
--   $$g_{i,x}(y)=\mathbf 1\bigl[\mathrm{Ratio}_{a\to b}(x,y)\le C_i(b\mid a)+\varepsilon_n\ \text{for all }a,b\bigr],\qquad\varepsilon_n=1/M .$$
--   The **access test**: $\mathrm{Gen}_{\mathrm{acc},i}$ samples a uniform word $\Omega_i\in\mathcal X^n$, $\mathrm{Word}_{\mathrm{acc},i}(\Omega_i)=\Omega_i$ and $A_{\Omega_i}(y)=g_{i,\Omega_i}(y)$, with $n=n_{\mathrm{acc}}=M^3$ when $k>1$.
--
--   The module also fixes $n_{\mathrm{acc}}$ ($0$ when $k=1$) and the family $\mathrm{apx}$ of **public rational upper approximations** $C_i(y\mid x)\le\mathrm{apx}_\lambda(i,x,y)\le C_i(y\mid x)+2^{-\lambda}$, each computed from $1^\lambda$ in polynomial time (Definition 4.1: "efficiently approximable"), used in numerical comparisons.
--
--   **Formalization Note** The channel probability in (5.9) is $\mathrm{apx}$ (§5 Conventions, p.21). For $k=1$ the test is the trivial test that always accepts.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §5 Conventions, p.21; §5.2.1, pp.24–25; Construction 5.6, p.25

import Mathlib
import Definitions.Def_NoisyOWMPC_Halves
import Definitions.Def_NoisyOWMPC_symEnc
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_QAdvFew_PoQOracle_tup

namespace NoisyOWMPC

variable {k : ℕ} {X : Type} [Fintype X] {Y : Fin k → Type} [∀ i, Fintype (Y i)]

/-- The binary encoding of a rational number: its sign bit, the absolute value of its numerator and
its denominator, each in binary. -/
def ratEnc (q : ℚ) : List Bool :=
  QAdvFew.PoQOracle.tup [[decide (q < 0)], KarpLiptonOM.binW (Nat.size q.num.natAbs) q.num.natAbs,
    KarpLiptonOM.binW (Nat.size q.den) q.den]

/-- `apx` is a family of **public rational upper approximations within `2^{−λ}`** of the channel
probabilities (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256 3a9569fa…), §5 Conventions,
p.21: "In numerical comparisons defining the access and release tests, channel probabilities denote
fixed public rational upper approximations within `2^{−λ}`, chosen deterministically for each
`λ`"): `C_i(y | x) ≤ apx_λ(i, x, y) ≤ C_i(y | x) + 2^{−λ}`, and each entry is computed from `1^λ`
in polynomial time (Definition 4.1, p.18: "the transition probabilities are public constants that
are efficiently approximable: a polynomial-time algorithm computes each `C(y | x)` to within `2^{−t}`
on input `1^t`").

**Formalization Note** The rational `apx_λ(i, x, y)` is output as its sign, numerator and denominator
in binary (`ratEnc`); the alphabets are fixed, so one machine per entry is one machine with a
constant table. -/
def IsApx (C : ∀ i, DMC X (Y i)) (apx : ℕ → ∀ i, X → Y i → ℚ) : Prop :=
  (∀ lam i x y, (C i).P x y ≤ (apx lam i x y : ℝ) ∧
    (apx lam i x y : ℝ) ≤ (C i).P x y + (2 : ℝ) ^ (-(lam : ℤ))) ∧
  ∀ i x y, LaconicBarrier.PolyTimeOn (ι := ℕ) (fun lam => [LaconicBarrier.unary lam])
    (fun lam => ratEnc (apx lam i x y))

open Classical in
/-- `Ratio_{a→b}(x, y) = N_{a,b}(x, y)/N_a(x)` if `N_a(x) > 0` and `0` otherwise (STOC 2027
submission (manuscript sha256 3a9569fa…), §5.2.1 Parameters, p.24), with
`N_a(x) = |{s : x_s = a}|` and `N_{a,b}(x, y) = |{s : x_s = a, y_s = b}|`. -/
noncomputable def ratio {L : ℕ} {Yi : Type} (x : Fin L → X) (y : Fin L → Yi) (a : X) (b : Yi) : ℚ :=
  if 0 < (Finset.univ.filter fun s => x s = a).card then
    ((Finset.univ.filter fun s => x s = a ∧ y s = b).card : ℚ) /
      ((Finset.univ.filter fun s => x s = a).card : ℚ)
  else 0

/-- The access channel-input length `n_acc = M³` (§5.2.1 Parameters, p.24), and `0` when `k = 1`
(no access cells; Theorem 5.24, p.30: "`1[k > 1] kM³` …"). -/
def nAcc (k : ℕ) (M : ℕ → ℕ) (lam : ℕ) : ℕ := if 1 < k then M lam ^ 3 else 0

open Classical in
/-- The **global Ratio predicate** (5.9) (§5.2.1, p.24): `g_{i,x}(y) = 1[Ratio_{a→b}(x, y) ≤
C_i(b | a) + ε_n for all a ∈ X, b ∈ Y_i]` with `ε_n = 1/M`, the channel probability being its
rational upper approximation `apx`. -/
noncomputable def accPred (apx : ℕ → ∀ i, X → Y i → ℚ) (i : Fin k) (M : ℕ) (lam : ℕ) {n : ℕ}
    (Ω : Fin n → X) (y : Fin n → Y i) : Bool :=
  decide (∀ a b, ratio Ω y a b ≤ apx lam i a b + 1 / (M : ℚ))

/-- **Construction 5.6 (Access test), protocol half** (STOC 2027 submission (manuscript sha256
3a9569fa…), p.25): `Gen_acc,i(1^λ)` samples a uniform word `Ω_i ∈ Xⁿ`, `Word_acc,i(Ω_i) = Ω_i`, and
`A_{Ω_i}(y) = g_{i,Ω_i}(y)`, with `n = M³` (p.24).

**Formalization Note** The word length `n` is a parameter (`n = M³`, p.24; `accessHalf` below
uses the protocol's `n_acc`). For `k = 1` this is the trivial access test of Definition 5.2 (p.22): length
`0`, one state, every query accepted. The sender's state is encoded by its symbols. -/
noncomputable def accessHalfN (apx : ℕ → ∀ i, X → Y i → ℚ) (M : ℕ → ℕ) (i : Fin k) (n : ℕ → ℕ) :
    TestHalf X (Y i) n where
  Sec lam := Fin (n lam) → X
  genW lam := unifW _
  enc _ Ω := wordEnc X Ω
  word _ Ω := Ω
  test lam Ω y := if 1 < k then accPred apx i (M lam) lam Ω y else true

/-- The access test of Construction 5.6 at the channel-input length `n_acc` of the protocol
(`M³` when `k > 1`, and `0` when `k = 1`). -/
noncomputable def accessHalf (apx : ℕ → ∀ i, X → Y i → ℚ) (M : ℕ → ℕ) (i : Fin k) :
    TestHalf X (Y i) (nAcc k M) :=
  accessHalfN apx M i (nAcc k M)

end NoisyOWMPC


