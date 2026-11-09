-- Prove2me | Definitions.Def_NoisyOWMPC_DMC
-- name    : NoisyOWMPC_DMC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:40:56.270459+00:00
-- url     : https://prove2.me/theorems/2c3e1efe-ba73-4dc8-99a5-f44237db044b
-- title:
--   Discrete memoryless channels, product broadcast channels and degradation
-- statement:
--   A **discrete memoryless channel** $C:\mathcal X\to\mathcal Y$ between finite alphabets is given by its stochastic matrix $C(y\mid x)=\Pr[C(x)=y]$. For $k$ receivers with channels $C_i:\mathcal X\to\mathcal Y_i$ on a common input alphabet, the **product broadcast channel** is
--   $$\mathbf C(y_1,\dots,y_k\mid x)=\prod_{i=1}^k C_i(y_i\mid x),$$
--   and $\mathbf C_{-i}$ is the channel whose output is the coordinates $j\neq i$ (for $k=1$ it has a single output). A **stochastic map** $K:\mathcal A\to\mathcal B$ is a matrix with nonnegative rows summing to one. **Stochastic degradation** $B\preceq E$ of $B:\mathcal X\to\mathcal Y$ by $E:\mathcal X\to\mathcal Z$ means $B=EK$ for a stochastic $K:\mathcal Z\to\mathcal Y$, that is $B(y\mid x)=\sum_z E(z\mid x)K(y\mid z)$. A channel is **nonconstant** if two inputs have different output distributions.
--
--   These are the channel model of the mission (Definition 4.1, §4.1, §4.3).
--
--   **Formalization Note** The alphabets are Lean types fixed independently of $\lambda$; the i.i.d. extension $C^N$ is the product of the entries over positions, written where it is used.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition 4.1 and §4.1, p.18; §4.3, p.20; Construction 5.23, p.30

import Mathlib

namespace NoisyOWMPC

/-- A **discrete memoryless channel** `C : X → Y` (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Definition 4.1, p.18: "a randomized map with finite input alphabet
`X` and finite output alphabet `Y`. Its stochastic matrix has entries `C(y | x) = Pr[C(x) = y]`"),
given by its stochastic matrix.

**Formalization Note** The alphabets are Lean types fixed independently of `λ`; the i.i.d. extension
`Cᴺ` is the product of the entries over positions, written out where it is used. -/
structure DMC (X Y : Type) [Fintype Y] where
  /-- the transition probability `C(y | x)` -/
  P : X → Y → ℝ
  nonneg : ∀ x y, 0 ≤ P x y
  sum_one : ∀ x, ∑ y, P x y = 1

/-- A **stochastic map** `K : A → B` (a stochastic matrix with nonnegative rows summing to one;
§4.3, p.20). -/
def IsStoch {A B : Type} [Fintype B] (K : A → B → ℝ) : Prop :=
  (∀ a b, 0 ≤ K a b) ∧ ∀ a, ∑ b, K a b = 1

/-- The **product broadcast channel** `C(y₁, …, y_k | x) = ∏_{i=1}^k C_i(y_i | x)` of DMCs
`C_i : X → Y_i` with a common input alphabet (§4.1 Channels with multiple receivers, p.18). -/
def jointP {k : ℕ} {X : Type} {Y : Fin k → Type} [∀ i, Fintype (Y i)] (C : ∀ i, DMC X (Y i))
    (x : X) (y : ∀ i, Y i) : ℝ :=
  ∏ i, (C i).P x (y i)

/-- The channel `C_{−i} = C_{[k]∖{i}}` whose output is the coordinates `j ≠ i` (§4.1, p.18). For
`k = 1` its output type has one element, so it is the trivial channel with one output (p.20). -/
def minusP {k : ℕ} {X : Type} {Y : Fin k → Type} [∀ i, Fintype (Y i)] (C : ∀ i, DMC X (Y i))
    (i : Fin k) (x : X) (z : ∀ j : {j : Fin k // j ≠ i}, Y j) : ℝ :=
  ∏ j : {j : Fin k // j ≠ i}, (C j).P x (z j)

/-- **Stochastic degradation** `B ⪯ E` (§4.3 Postprocessing and degradation, p.20: "`B ⪯ E`, means
that `B = E K` for some stochastic map `K : Z → Y`"): `B(y | x) = ∑_z E(z | x) K(y | z)`. -/
def Degraded {X Yb Ze : Type} [Fintype Yb] [Fintype Ze] (B : X → Yb → ℝ) (E : X → Ze → ℝ) :
    Prop :=
  ∃ K : Ze → Yb → ℝ, IsStoch K ∧ ∀ x y, B x y = ∑ z, E x z * K z y

/-- A channel is **nonconstant** (§5.3, Construction 5.23, p.30: "nonconstant marginals `C_i`"):
two inputs have different output distributions. -/
def Nonconstant {X Y : Type} [Fintype Y] (D : DMC X Y) : Prop := ∃ x x', D.P x ≠ D.P x'

end NoisyOWMPC


