-- Prove2me | Definitions.Def_QLocalCert_Supplement_PathDQMA
-- name    : QLocalCert_Supplement_PathDQMA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:39:59.383214+00:00
-- url     : https://prove2.me/theorems/bfcd2bb3-e872-4999-b3a7-34794f50ccaa
-- title:
--   One-round dQMA protocols for equality on a path (Definition 18) and $q_\partial$
-- statement:
--   Let $v_0,\dots,v_r$ be the nodes of a path; $v_0$ holds $x\in\{0,1\}^N$ and $v_r$ holds $y\in\{0,1\}^N$. A **one-round dQMA protocol** for the equality problem $\mathrm{EQ}^2_N$ on this path consists of:
--
--   1. register sizes: $c(v_j)$ certificate qubits and a number of kept qubits at each node, and, on each edge $v_ev_{e+1}$, a number of qubits sent from $v_e$ to $v_{e+1}$ and from $v_{e+1}$ to $v_e$; their sum is $m(v_e,v_{e+1})$, the total number of qubits exchanged on that edge;
--   2. for each node an isometry $V_j$ mapping its certificate register to its kept part and its outgoing messages (to $v_{j+1}$ and to $v_{j-1}$);
--   3. for each node a two-outcome POVM $\{E_j, I-E_j\}$ on its kept part and the messages it receives.
--
--   Only $V_0, E_0$ may depend on $x$ and only $V_r, E_r$ on $y$; interior nodes hold no input. The prover supplies an arbitrary joint state $\rho$ on $\bigotimes_j\mathbb C^{2^{c(v_j)}}$; all nodes apply their isometries simultaneously, messages are delivered (by a permutation $W$ of registers), and each node measures. The probability that all nodes accept is
--   $$
--   \Pr[\mathrm{Acc}\mid x,y,\rho]=\operatorname{tr}\Big[\big(\textstyle\bigotimes_j E_j\big)\,W\big(\textstyle\bigotimes_j V_j\big)\rho\big(\textstyle\bigotimes_j V_j\big)^\dagger W^\dagger\Big].
--   $$
--   The protocol has completeness $c$ and soundness $s$ if for every $x$ some state is accepted on $(x,x)$ with probability at least $c$, and for all $x\ne y$ every state is accepted on $(x,y)$ with probability at most $s$.
--
--   For $r\ge2$, the boundary cost is
--   $$
--   q_\partial:=c(v_{r-1})+c(v_r)+m(v_{r-2},v_{r-1}),
--   $$
--   the certificate qubits of the two nodes nearest the endpoint holding $y$ plus all qubits exchanged on the edge $v_{r-2}v_{r-1}$.
--
--   This is the protocol model of Theorem 5 (upper bounds) and Theorem 21 (lower bound).
--
--   **Formalization Note** All sizes are functions $\mathbb N\to\mathbb N$ of which only the values at nodes $j\le r$ and edges $e<r$ are used; endpoints send nothing off the path (those registers have size $0$). The paper's prover state is pure; the model uses density operators, which gives the same maximal acceptance probabilities by convexity. Isometries followed by a two-outcome POVM subsume ancillas, private coins and classical messages.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Definition 18, p.32; q∂, p.32

import Mathlib
import Definitions.Def_QLocalCert_piKron
import Definitions.Def_WildeQIT_IsDensityOperator

open scoped ComplexOrder
set_option autoImplicit false

namespace QLocalCert.Supplement

open Matrix

/-- Copy a bit string of length `a` into a register of `b` bits (bits beyond `a` read `false`). It is
used only with `a = b`, where it is the identity map on basis strings, or with `b = 0`; it lets message
registers whose sizes agree only propositionally be identified without casts. -/
def readBits {a : ℕ} (src : Qb a) (b : ℕ) : Qb b :=
  fun i => if h : (i : ℕ) < a then src ⟨i, h⟩ else false

/-- One-round dQMA protocol for the two-party equality problem `EQ²_N` on the path
`v₀, …, v_r` (Definition 18).

B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Definition 18, p.32: "Let v0, . . . , vr be
nodes on a path; v0 holds x ∈ {0, 1}^N and vr holds y ∈ {0, 1}^N. A protocol specifies finite register
sizes and, for each node, input-dependent local operations, as follows. 1. The prover prepares an
arbitrary pure state ξ on ⊗_{j=0}^r H_j, where H_j has c(v_j) qubits, and node v_j receives H_j.
2. Simultaneously, each node applies an isometry to its register, producing a kept part and outgoing
message registers, and sends each message to the corresponding neighbour; m(v_j, v_{j+1}) denotes the
total qubits exchanged between v_j and v_{j+1}. The isometry of v0 may depend on x, that of vr on y.
3. Each node measures its kept part together with its incoming messages with a two-outcome POVM
(accept/reject). The POVM of v0 may depend on x, that of vr on y."

**Formalization Note.**
* Node `v_j` is `j : Fin (r + 1)`. Sizes are functions `ℕ → ℕ`; only `cert j`, `keep j` for
  `j ≤ r` and `fwd e`, `bwd e` for `e < r` matter. `cert j = c(v_j)` certificate qubits, `keep j`
  kept qubits; on the edge `v_e v_{e+1}` node `v_e` sends `fwd e` qubits to `v_{e+1}` and `v_{e+1}`
  sends `bwd e` qubits to `v_e`, so `m(v_e, v_{e+1}) = fwd e + bwd e`. All sizes may differ between
  nodes and edges, and none is bounded by the model.
* Node `j` applies `iso j z : ℂ^{2^cert j} → ℂ^{2^keep j} ⊗ (message to v_{j+1}) ⊗ (message to v_{j−1})`
  and then measures `{eff j z, I − eff j z}` (accept on `eff`) on its kept part ⊗ (message received
  from `v_{j−1}`) ⊗ (message received from `v_{j+1}`). The endpoint `v_0` sends nothing to the left and
  `v_r` nothing to the right (those registers have size 0).
* The argument `z` is the node's local input: `x` at `v_0`, `y` at `v_r`. Interior nodes hold no input:
  `iso_indep`, `eff_indep` say their operations do not depend on `z`.
* Isometries (with a final two-outcome POVM) subsume workspace ancillas, private coins and classical
  messages. The protocol is fixed with `N` and `r`. -/
structure PathDQMA (N r : ℕ) where
  /-- Certificate qubits `c(v_j)` of node `j`. -/
  cert : ℕ → ℕ
  /-- Kept qubits of node `j`. -/
  keep : ℕ → ℕ
  /-- Qubits sent from `v_e` to `v_{e+1}`. -/
  fwd : ℕ → ℕ
  /-- Qubits sent from `v_{e+1}` to `v_e`. -/
  bwd : ℕ → ℕ
  /-- The isometry of node `j` on local input `z`. Output: kept part, message to the right, message
  to the left. -/
  iso : (j : Fin (r + 1)) → (Fin N → Bool) →
    Matrix (Qb (keep j) × Qb (if (j : ℕ) < r then fwd j else 0) ×
      Qb (if 0 < (j : ℕ) then bwd ((j : ℕ) - 1) else 0)) (Qb (cert j)) ℂ
  /-- `V†V = I`. -/
  iso_isometry : ∀ j z, (iso j z)ᴴ * iso j z = 1
  /-- Interior nodes hold no input. -/
  iso_indep : ∀ j : Fin (r + 1), (j : ℕ) ≠ 0 → (j : ℕ) ≠ r → ∀ z z', iso j z = iso j z'
  /-- The accepting effect of node `j` on local input `z`, on its kept part, the message received
  from the left and the message received from the right. -/
  eff : (j : Fin (r + 1)) → (Fin N → Bool) →
    Matrix (Qb (keep j) × Qb (if 0 < (j : ℕ) then fwd ((j : ℕ) - 1) else 0) ×
        Qb (if (j : ℕ) < r then bwd j else 0))
      (Qb (keep j) × Qb (if 0 < (j : ℕ) then fwd ((j : ℕ) - 1) else 0) ×
        Qb (if (j : ℕ) < r then bwd j else 0)) ℂ
  /-- `0 ⪯ E`. -/
  eff_nonneg : ∀ j z, (eff j z).PosSemidef
  /-- `E ⪯ I`. -/
  eff_le_one : ∀ j z, (1 - eff j z).PosSemidef
  /-- Interior nodes hold no input. -/
  eff_indep : ∀ j : Fin (r + 1), (j : ℕ) ≠ 0 → (j : ℕ) ≠ r → ∀ z z', eff j z = eff j z'

namespace PathDQMA

variable {N r : ℕ} (P : PathDQMA N r)

/-- The joint basis after the isometries: at each node, its kept part and its two outgoing
messages. -/
abbrev Sent := ∀ j : Fin (r + 1), Qb (P.keep j) × Qb (if (j : ℕ) < r then P.fwd j else 0) ×
  Qb (if 0 < (j : ℕ) then P.bwd ((j : ℕ) - 1) else 0)

/-- The joint basis after delivery: at each node, its kept part and its two incoming messages. -/
abbrev Recv := ∀ j : Fin (r + 1), Qb (P.keep j) ×
  Qb (if 0 < (j : ℕ) then P.fwd ((j : ℕ) - 1) else 0) × Qb (if (j : ℕ) < r then P.bwd j else 0)

/-- Message delivery on basis configurations: node `j` receives the right-going message of
`v_{j−1}` and the left-going message of `v_{j+1}` (sizes agree; at the endpoints the missing register
has size 0). This is a bijection of basis configurations. -/
def recv (X : P.Sent) : P.Recv := fun j =>
  ((X j).1,
   readBits (X ⟨(j : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.2⟩).2.1 _,
   readBits (X ⟨min ((j : ℕ) + 1) r, lt_of_le_of_lt (min_le_right _ _) (Nat.lt_succ_self r)⟩).2.2 _)

/-- The local input of node `j` on the instance `(x, y)`: `x` at `v_0`, `y` elsewhere (only `v_r`'s
operations depend on it, for `r ≥ 1`). -/
def input (x y : Fin N → Bool) (j : Fin (r + 1)) : Fin N → Bool :=
  if (j : ℕ) = 0 then x else y

/-- The probability that all nodes accept on the instance `(x, y)` when the prover's joint certificate
is the density operator `ρ` on `⊗_j ℂ^{2^{c(v_j)}}` (arbitrarily entangled):
`tr[(⊗_j E_j) · W (⊗_j V_j) ρ (⊗_j V_j)† W†]`, `W` the delivery permutation. -/
noncomputable def acceptProb (x y : Fin N → Bool)
    (ρ : Matrix (∀ j : Fin (r + 1), Qb (P.cert j)) (∀ j : Fin (r + 1), Qb (P.cert j)) ℂ) : ℝ :=
  let V : Matrix P.Sent (∀ j : Fin (r + 1), Qb (P.cert j)) ℂ :=
    piKron fun j => P.iso j (input x y j)
  let E : Matrix P.Recv P.Recv ℂ := piKron fun j => P.eff j (input x y j)
  (trace (E.submatrix P.recv P.recv * (V * ρ * Vᴴ))).re

/-- Definition 18, p.32: the protocol has completeness `c` and soundness `s` for `EQ²_N`: "for `x = y`
some proof makes all nodes accept with probability ≥ c, and for `x ≠ y`, every proof makes all nodes
accept with probability ≤ s". Proofs range over all density operators on the joint certificate space
(by convexity, the same as pure states). -/
def Correct (c s : ℝ) : Prop :=
  (∀ x : Fin N → Bool, ∃ ρ, WildeQIT.IsDensityOperator ρ ∧ c ≤ P.acceptProb x x ρ) ∧
  (∀ x y : Fin N → Bool, x ≠ y → ∀ ρ, WildeQIT.IsDensityOperator ρ → P.acceptProb x y ρ ≤ s)

/-- `q∂ := c(v_{r−1}) + c(v_r) + m(v_{r−2}, v_{r−1})` (p.32), the certificate qubits of the two nodes
nearest the endpoint holding `y` plus all qubits exchanged on the edge `v_{r−2} v_{r−1}`. Meaningful
for `r ≥ 2`. -/
def qBoundary : ℕ := P.cert (r - 1) + P.cert r + (P.fwd (r - 2) + P.bwd (r - 2))

end PathDQMA

end QLocalCert.Supplement


