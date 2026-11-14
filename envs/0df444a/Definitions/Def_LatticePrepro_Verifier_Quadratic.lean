-- Prove2me | Definitions.Def_LatticePrepro_Verifier_Quadratic
-- name    : LatticePrepro_Verifier_Quadratic
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:19:14.793774+00:00
-- url     : https://prove2.me/theorems/d3360b63-9862-48f2-9f65-804896a6388d
-- title:
--   Quadratic verifiers and encoding tuples (Definitions 3.13–3.14, Claim 3.15, Construction 4.5)
-- statement:
--   Fix a prime $p$ and write $\mathbb{F}_p = \mathbb{Z}/p\mathbb{Z}$.
--
--   - **Quadratic verifier** (`QuadraticVerifier p`): an instance length $n$, a number $S \ge n + 1$ of assignment coordinates, a number $G$ of gate equations, and coefficients $c^{(b)}_{ij} \in \mathbb{F}_p$ for each gate $b$ and $0 \le i, j \le S$. Assignments are vectors $z = (z_0, z_1, \dots, z_S) \in \mathbb{F}_p^{S+1}$, where $z_0$ is the constant coordinate.
--   - **Gate equations and validity** (`gateEq`, `IsValid`): $Q_b(z) = \sum_{i=0}^{S}\sum_{j=0}^{S} c^{(b)}_{ij}\, z_i z_j$, and $z$ is valid if $Q_b(z) = 0$ for every $b$.
--   - **Boolean assignments** (`IsBooleanAssignment`): $z_0 = 1$ and $z_i \in \{0,1\}$ for all $i$.
--   - **Coordinates**: the input coordinates are $1, \dots, n$ (`inputIdx`), the output coordinate is $n+1$ (`outputIdx`), and the auxiliary coordinates are those $i$ with $n+1 < i \le S$ (`AuxIdx`).
--   - **Prefix and acceptance** (`HasPrefix`, `IsAccepting`): for an instance $x = (x_1, \dots, x_n) \in \{0,1\}^n$, $z$ has prefix $(x, 1)$ if $z_i = x_i$ for $1 \le i \le n$ and $z_{n+1} = 1$; $z$ is accepting on $x$ if it is Boolean, valid and has prefix $(x, 1)$. The **language** is $L(V) = \{x : \text{some } z \text{ is accepting on } x\}$.
--   - `assignOf x u`: the assignment $(1, x_1, \dots, x_n, 1, u_{n+2}, \dots, u_S)$ with values $u$ on the auxiliary coordinates.
--   - **Encoding tuple** (`EncodingTuple p K S`, for a field $K$ that is an $\mathbb{F}_p$-algebra): elements $E_0, E_1, \dots, E_S \in K$ with $E_0 = 0$ and $E_1, \dots, E_S$ linearly independent over $\mathbb{F}_p$; the **encoding** of an assignment is
--   $$\mathrm{enc}(z) = \sum_{i=0}^{S} z_i\, E_i \in K.$$
--   - **Instance encoding** (`instanceEnc`): $\theta_x = \mathrm{enc}(\mathrm{assignOf}(x, 0)) = \sum_{i=1}^{n} x_i E_i + E_{n+1}$.
--
--   All main results of the formalization (Construction 4.5, Theorems 4.6 and 4.8, and Theorem 5.1 for general verifiers) are stated for an arbitrary quadratic verifier; Boolean circuits (Definition 3.13) are converted into quadratic verifiers with the same language via Claim 3.15. The encoding tuple $E$ and the instance encoding $\theta_x$ are ingredients of Construction 4.5.
--
--   **Formalization Note**: The paper's verifier is a Boolean circuit; here a verifier is abstracted as the system of quadratic gate equations of Claim 3.15 with a designated input prefix and output coordinate, in the coordinate order of Definition 3.14 (inputs, output, then witness and remaining gate outputs). Lean indexes instances by `Fin n` (so $x_i$ above is `x ⟨i-1, _⟩`), stores Boolean bits as $0/1 \in \mathbb{F}_p$, and indexes $E$ by `Fin (S+1)` with the convention $E_0 = 0$ so that sums run over all coordinates.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Definitions 3.13–3.14 (\label{def:verifier}, \label{def:computation-assignment}), Claim 3.15 (\label{clm:verifier-system}) and Construction 4.5 (\label{con:fixed-verifier}); Lean: LatticePrepro/Verifier/Quadratic.lean, LatticePrepro.QuadraticVerifier, LatticePrepro.EncodingTuple, LatticePrepro.QuadraticVerifier.instanceEnc

import Mathlib

/-!
# Quadratic verifiers and encodings

The moment reduction only uses a verifier through a system of homogeneous quadratic equations
over `𝔽_p` in the coordinates `(z_0, z_1, …, z_S)` with `z_0 = 1` (Claim 3.15 of the paper
produces such a system from a Boolean circuit with fan-in-two gates).

We therefore abstract a verifier as a `QuadraticVerifier`: it has `S` assignment coordinates
(indexed by `Fin (S+1)`, where index `0` is the constant coordinate), `n` input coordinates
(indices `1, …, n`), the output coordinate `n + 1`, and `G` quadratic *gate equations*.

An assignment is *valid* if all gate equations vanish, and *accepting on `x`* if it is valid,
Boolean, and has prefix `(x, 1)`. The language of the verifier is the set of instances with
an accepting assignment (Definitions 3.13 and 3.14).

We also define *encoding tuples* `E = (E_1, …, E_S)` of `𝔽_p`-linearly independent elements of
a field `K`, the encoding `enc z = ∑ E_i z_i` of an assignment, and the instance encoding
`θ_x = enc (x, 1, 0, …, 0)`.
-/

namespace LatticePrepro

/-- A quadratic verifier over `ZMod p` (cf. Definitions 3.13, 3.14 and Claim 3.15). -/
structure QuadraticVerifier (p : ℕ) where
  /-- Instance length. -/
  n : ℕ
  /-- Number of assignment coordinates (excluding the constant coordinate `0`). -/
  S : ℕ
  /-- The prefix `(x, 1)` fits into the assignment. -/
  n_succ_le : n + 1 ≤ S
  /-- Number of gate equations. -/
  G : ℕ
  /-- Coefficients `c^{(b)}_{(i,j)}` of the gate equations. -/
  coeff : Fin G → Fin (S + 1) → Fin (S + 1) → ZMod p

namespace QuadraticVerifier

variable {p : ℕ} (V : QuadraticVerifier p)

/-- The value `Q_b(z) = ∑ c_{ij} z_i z_j` of the `b`-th gate equation. -/
def gateEq (b : Fin V.G) (z : Fin (V.S + 1) → ZMod p) : ZMod p :=
  ∑ i, ∑ j, V.coeff b i j * (z i * z j)

/-- An assignment is valid if all gate equations vanish. -/
def IsValid (z : Fin (V.S + 1) → ZMod p) : Prop := ∀ b, V.gateEq b z = 0

/-- Boolean assignments with constant coordinate `1`. -/
def IsBooleanAssignment (z : Fin (V.S + 1) → ZMod p) : Prop :=
  z 0 = 1 ∧ ∀ i, z i = 0 ∨ z i = 1

/-- The index of the `i`-th input coordinate (`1 ≤ i + 1 ≤ n`). -/
def inputIdx (i : Fin V.n) : Fin (V.S + 1) := ⟨i.val + 1, by have := V.n_succ_le; omega⟩

/-- The index `n + 1` of the output coordinate. -/
def outputIdx : Fin (V.S + 1) := ⟨V.n + 1, by have := V.n_succ_le; omega⟩

/-- Indices `i > n + 1` of the remaining (witness and gate) coordinates. -/
abbrev AuxIdx : Type := {i : Fin (V.S + 1) // V.n + 1 < i.val}

/-- The assignment has prefix `(x, 1)`. -/
def HasPrefix (x : Fin V.n → Bool) (z : Fin (V.S + 1) → ZMod p) : Prop :=
  (∀ i, z (V.inputIdx i) = if x i then 1 else 0) ∧ z V.outputIdx = 1

/-- Accepting computation on `x` (Definition 3.14). -/
def IsAccepting (x : Fin V.n → Bool) (z : Fin (V.S + 1) → ZMod p) : Prop :=
  V.IsBooleanAssignment z ∧ V.IsValid z ∧ V.HasPrefix x z

/-- The language accepted by the verifier. -/
def Language : Set (Fin V.n → Bool) := {x | ∃ z, V.IsAccepting x z}

/-- The canonical assignment with prefix `(x, 1)` and values `u` on the auxiliary coordinates. -/
def assignOf (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) : Fin (V.S + 1) → ZMod p :=
  fun i =>
    if h0 : i.val = 0 then 1
    else if hn : i.val ≤ V.n then (if x ⟨i.val - 1, by omega⟩ then 1 else 0)
    else if hout : i.val = V.n + 1 then 1
    else u ⟨i, by omega⟩

end QuadraticVerifier

/-- An encoding tuple: `𝔽_p`-linearly independent elements `E_1, …, E_S` of `K`, indexed by
`Fin (S+1)` with the convention `E_0 = 0`. -/
structure EncodingTuple (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K]
    (S : ℕ) where
  /-- The elements `E_0 = 0, E_1, …, E_S`. -/
  E : Fin (S + 1) → K
  E_zero : E 0 = 0
  linearIndependent : LinearIndependent (ZMod p) (fun i : Fin S => E i.succ)

namespace EncodingTuple

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] {S : ℕ}
  (ε : EncodingTuple p K S)

/-- The encoding `∑ i, z_i • E_i` of an assignment. -/
def enc (z : Fin (S + 1) → ZMod p) : K := ∑ i, z i • ε.E i

end EncodingTuple

namespace QuadraticVerifier

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  (V : QuadraticVerifier p) (ε : EncodingTuple p K V.S)

/-- The instance encoding `θ_x = enc (x, 1, 0, …, 0)`. -/
def instanceEnc (x : Fin V.n → Bool) : K := ε.enc (V.assignOf x 0)

end QuadraticVerifier

end LatticePrepro


