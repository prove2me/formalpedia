-- Prove2me | Definitions.Def_PoQHierarchy_Main_NonlocalGame
-- name    : PoQHierarchy_Main_NonlocalGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:48.626457+00:00
-- url     : https://prove2.me/theorems/ccfc1e13-9f40-4872-a103-b1b3e843a799
-- title:
--   Nonlocal games, the classical value $\omega_c$, the quantum value $\omega_q$, and gate-set circuit strategies
-- statement:
--   An **$n$-player nonlocal game** (Definition 3.2) is $G=(I_1,\dots,I_n,O_1,\dots,O_n,\mu,V)$ with finite question sets $I_i$ and answer sets $O_i$, a probability distribution $\mu$ on $I_1\times\cdots\times I_n$ and a predicate $V(a_1,\dots,a_n,x_1,\dots,x_n)\in\{0,1\}$. The winning probability of a correlation $p(a\mid x)$ is
--   $$\sum_x\mu(x)\sum_a V(a,x)\,p(a\mid x).$$
--
--   - A **classical strategy** has shared randomness $\ell\sim\pi$ on a finite set and deterministic responses $a_i=f_i(\ell,x_i)$. The **classical value** $\omega_c(G)$ is the supremum of their winning probabilities.
--   - A **quantum strategy** gives player $i$ the space $\mathbb C^{d_i}$, a shared unit vector $\psi\in\mathbb C^{d_1}\otimes\cdots\otimes\mathbb C^{d_n}$ and, for every question $x$, a POVM $\{E^{(i)}_{x,a}\}_a$ on the player's factor, with correlation $\langle\psi|E^{(1)}_{x_1a_1}\otimes\cdots\otimes E^{(n)}_{x_na_n}|\psi\rangle$. The **quantum value** $\omega_q(G)$ is the supremum of their winning probabilities (p.17, p.20).
--   - A **circuit strategy** is a quantum strategy given by circuits over $\{CX,H,T\}$: $W$ qubits, each owned by one player; a state-preparation circuit applied to $|0\cdots0\rangle$; and for every player and question a circuit on the player's own qubits, a list of its qubits to measure, and a classical map from the outcome to an answer. These are the strategies whose circuits the KLVY compiler evaluates homomorphically (p.22).
--
--   **Formalization Note** $I_i=\{0,\dots,q_i-1\}$ and $O_i=\{0,\dots,o_i-1\}$ (`Fin`). That $\mu$ is a distribution is the separate predicate `IsValid`. Shared quantum states are pure; a mixed state is purified within a larger finite-dimensional factor, which changes no correlation.
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), Definition 3.2 (p.19), p.17 (n-partite quantum correlations), p.20 (values ω_c, ω_q), p.22 (circuits evaluated by the compiler); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_Device

open QAlgorithms.Complexity
open scoped ComplexOrder
set_option autoImplicit false

namespace PoQHierarchy.Main

/-!
Bacho, Leichtle, Arora, Cojocaru, STOC 2027 submission #1666, Definition 3.2 (p.19) and the values
of p.20 and p.17: nonlocal games, classical strategies with shared randomness (value `ω_c`),
finite-dimensional tensor-product quantum strategies (value `ω_q`), and quantum strategies given by
circuits over the gate set `{CX, H, T}` (the strategies the KLVY compiler evaluates, p.22).

Players are `Fin n` (`0, …, n-1` for the paper's `1, …, n`); the question and answer sets of player
`i` are `Fin (q i)` and `Fin (o i)`.
-/

/-- An `n`-player nonlocal game `G = (I_1, …, I_n, O_1, …, O_n, μ, V)` (Definition 3.2), with
`I_i = Fin (q i)`, `O_i = Fin (o i)`, the question distribution `μ` and the predicate `V(a, x)`.
That `μ` is a probability distribution is the predicate `IsValid`. -/
structure NonlocalGame (n : ℕ) where
  q : Fin n → ℕ
  o : Fin n → ℕ
  μ : ((i : Fin n) → Fin (q i)) → ℝ
  V : ((i : Fin n) → Fin (o i)) → ((i : Fin n) → Fin (q i)) → Bool

namespace NonlocalGame

variable {n : ℕ} (G : NonlocalGame n)

/-- `μ` is a probability distribution on `I_1 × ⋯ × I_n`. -/
def IsValid : Prop := (∀ x, 0 ≤ G.μ x) ∧ ∑ x, G.μ x = 1

/-- The winning probability of a correlation `p(a | x)`: `∑_x μ(x) ∑_a V(a,x) p(a|x)`. -/
noncomputable def winOf (p : ((i : Fin n) → Fin (G.o i)) → ((i : Fin n) → Fin (G.q i)) → ℝ) : ℝ :=
  ∑ x, G.μ x * ∑ a, if G.V a x then p a x else 0

end NonlocalGame

/-! ### Classical strategies with shared randomness -/

/-- A classical strategy with shared randomness: a finite random seed `l ~ π` and deterministic
response functions `f_i(l, x_i)`. -/
structure ClassicalStrategy {n : ℕ} (G : NonlocalGame n) where
  Λ : Type
  [fin : Fintype Λ]
  π : Λ → ℝ
  π_nonneg : ∀ l, 0 ≤ π l
  π_sum : ∑ l, π l = 1
  f : (i : Fin n) → Λ → Fin (G.q i) → Fin (G.o i)

attribute [instance] ClassicalStrategy.fin

/-- Its correlation `p(a|x) = ∑_l π(l) [f_i(l, x_i) = a_i for all i]`. -/
noncomputable def ClassicalStrategy.corr {n : ℕ} {G : NonlocalGame n} (S : ClassicalStrategy G)
    (a : (i : Fin n) → Fin (G.o i)) (x : (i : Fin n) → Fin (G.q i)) : ℝ :=
  ∑ l, if ∀ i, S.f i l (x i) = a i then S.π l else 0

/-- The classical value `ω_c(G)` (p.20): the supremum of the winning probabilities of classical
strategies. -/
noncomputable def omegaC {n : ℕ} (G : NonlocalGame n) : ℝ :=
  sSup {v | ∃ S : ClassicalStrategy G, G.winOf S.corr = v}

/-! ### Finite-dimensional quantum strategies -/

/-- A quantum strategy (p.17, p.20): player `i` holds `ℂ^{d_i}`, the players share a unit vector
`ψ ∈ ℂ^{d_1} ⊗ ⋯ ⊗ ℂ^{d_n}`, and for each question `x` player `i` has a POVM `{E^{(i)}_{x,a}}_a` on
its own factor. -/
structure QuantumStrategy {n : ℕ} (G : NonlocalGame n) where
  d : Fin n → ℕ
  ψ : ((i : Fin n) → Fin (d i)) → ℂ
  ψ_norm : ∑ z, Complex.normSq (ψ z) = 1
  E : (i : Fin n) → Fin (G.q i) → Fin (G.o i) → Matrix (Fin (d i)) (Fin (d i)) ℂ
  E_psd : ∀ i x a, (E i x a).PosSemidef
  E_sum : ∀ i x, ∑ a, E i x a = 1

/-- Its correlation `p(a|x) = ⟨ψ| E^{(1)}_{x_1 a_1} ⊗ ⋯ ⊗ E^{(n)}_{x_n a_n} |ψ⟩`. -/
noncomputable def QuantumStrategy.corr {n : ℕ} {G : NonlocalGame n} (S : QuantumStrategy G)
    (a : (i : Fin n) → Fin (G.o i)) (x : (i : Fin n) → Fin (G.q i)) : ℂ :=
  ∑ z, ∑ z', star (S.ψ z) * (∏ i, S.E i (x i) (a i) (z i) (z' i)) * S.ψ z'

/-- The quantum value `ω_q(G)` (p.20). -/
noncomputable def omegaQ {n : ℕ} (G : NonlocalGame n) : ℝ :=
  sSup {v | ∃ S : QuantumStrategy G, G.winOf (fun a x => (S.corr a x).re) = v}

/-! ### Quantum strategies given by circuits over the gate set -/

/-- The qubits a gate acts on. -/
def Gate.wires : Gate → List ℕ
  | .cx c d => [c, d]
  | .h i => [i]
  | .t i => [i]

/-- A quantum strategy given by circuits over `{CX, H, T}`: `W` qubits, each owned by one player; a
state-preparation circuit applied to `|0…0⟩`; and, for each player and question, a circuit on the
player's own qubits, a list of its own qubits to measure, and a classical map from the outcome to an
answer. -/
structure CircStrategy {n : ℕ} (G : NonlocalGame n) where
  W : ℕ
  owner : Fin W → Fin n
  prep : List Gate
  gates : (i : Fin n) → Fin (G.q i) → List Gate
  meas : (i : Fin n) → Fin (G.q i) → List ℕ
  ans : (i : Fin n) → Fin (G.q i) → Str → Fin (G.o i)
  prep_wf : ∀ g ∈ prep, g.WellFormed W = true
  gates_local : ∀ i x, ∀ g ∈ gates i x, g.WellFormed W = true ∧
    ∀ w ∈ g.wires, ∃ h : w < W, owner ⟨w, h⟩ = i
  meas_local : ∀ i x, ∀ w ∈ meas i x, ∃ h : w < W, owner ⟨w, h⟩ = i

/-- Measuring the lists of qubits `ms` one after the other: the branches, each with the list of
outcome strings and the unnormalized post-measurement state. -/
def measureAll {W : ℕ} (ms : List (List ℕ)) (ψ : QVec W) : List (List Str × QVec W) :=
  ms.foldl (fun acc m => acc.flatMap fun p =>
    (allStrings m.length).map fun b => (p.1 ++ [b], project m b p.2)) [([], ψ)]

/-- The winning probability of a circuit strategy: prepare the state, let every player apply its
circuit for its question and measure, map outcomes to answers, and check the predicate. -/
noncomputable def CircStrategy.win {n : ℕ} {G : NonlocalGame n} (S : CircStrategy G) : ℝ :=
  ∑ x, G.μ x *
    let ψx := applyGates ((List.finRange n).flatMap fun i => S.gates i (x i))
      (applyGates S.prep (zeroVec S.W))
    ((measureAll ((List.finRange n).map fun i => S.meas i (x i)) ψx).map fun p =>
      if G.V (fun i => S.ans i (x i) (p.1.getD i.val [])) x then normSq p.2 else 0).sum

end PoQHierarchy.Main


