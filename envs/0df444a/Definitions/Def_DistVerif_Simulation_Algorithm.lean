-- Prove2me | Definitions.Def_DistVerif_Simulation_Algorithm
-- name    : DistVerif_Simulation_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:16.863409+00:00
-- url     : https://prove2.me/theorems/d4684038-ed82-44d2-b031-f68b80501f8d
-- title:
--   B-model distributed algorithms, executions $\sigma_{\mathcal A}(v,t,x,y)$, public coins and $\epsilon$-error (§1.1, §2.1, §2.3)
-- statement:
--   A **synchronous network in the B model** is an undirected graph $G$ on a vertex set $V$ whose vertices are processors with unbounded computational power; in every round each vertex may send a message of $B$ bits along each incident edge in each direction. Two designated vertices $s$ and $r$ receive the inputs: $s$ gets a $b$-bit string $x\in\{0,1\}^b$, $r$ gets $y\in\{0,1\}^b$, and no other vertex receives input.
--
--   A **deterministic distributed algorithm** $\mathcal A$ consists of a set of local states; initial states for $s$ (depending on $x$), for $r$ (depending on $y$) and for every other vertex (depending only on the vertex); a sending rule, giving the $B$-bit message a vertex in a given state sends to a given neighbour; a transition rule, giving the new state of a vertex from its current state and the messages it has just received from its neighbours; and output maps reading a bit off the states of $s$ and $r$.
--
--   The **execution** $\varphi_{\mathcal A}(x,y)$ is defined round by round. $\sigma_{\mathcal A}(v,0,x,y)$ is the initial state of $v$. In round $t+1$ every vertex $w$ sends to each neighbour $v$ the message computed from $\sigma_{\mathcal A}(w,t,x,y)$, and $v$ then moves to $\sigma_{\mathcal A}(v,t+1,x,y)$, computed from $\sigma_{\mathcal A}(v,t,x,y)$ and the messages it received. Thus the state of $v$ at the end of round $t$ is determined by its input and the messages on its incoming links in rounds $1,\dots,t$.
--
--   A **public-coin randomized algorithm** is a random string $\omega$, drawn from a probability distribution $\mu$ and seen by all vertices, together with a deterministic algorithm $\mathcal A_\omega$ for each $\omega$. For $f:\{0,1\}^b\times\{0,1\}^b\to\{0,1\}$, $\epsilon\in\mathbb R$ and $T\in\mathbb N$, the algorithm **computes $f$ with $\epsilon$-error in $T$ rounds** if for every input pair $(x,y)$
--   $$\mu\Big(\big\{\omega : \text{after round } T,\ s \text{ or } r \text{ under } \mathcal A_\omega \text{ does not output } f(x,y)\big\}\Big)\le\epsilon .$$
--
--   These are the objects of the quantity $R^G_\epsilon(f)$ of the paper: the worst-case running time of the best $\epsilon$-error randomized distributed algorithm computing $f$ on $G$, with both $s$ and $r$ required to output $f(x,y)$.
--
--   **Formalization Note** A message is exactly `Fin B → Bool`, and every directed edge carries one in every round; the paper says "at most $B$ bits" (p. 1237) but counts $B$-bit messages in Lemma 3.4, and with variable-length or optional messages silence would carry information. A vertex receives a fixed all-`false` dummy from every non-neighbour, so it cannot read non-neighbours. Inputs enter only through the initial states of $s$ and $r$. Local rules may depend on the vertex's identity. Running time is a fixed number $T$ of rounds with outputs read after round $T$; this is equivalent to the paper's worst case over inputs and random strings (§2.1), since a run that finishes earlier can idle. The randomness is a `PMF` on an arbitrary type `Ω`, and the error event is measured with `PMF.toOuterMeasure`; $\epsilon$ enters through `ENNReal.ofReal`, so theorems assume $\epsilon\ge0$.
-- source:
--   Das Sarma, Holzer, Kor, Korman, Nanongkai, Pandurangan, Peleg, Wattenhofer, Distributed Verification and Hardness of Distributed Approximation, SIAM J. Comput. 41 (2012), p. 1237, §1.1 (the B model); p. 1243, §2.1 (ε-error, public coin, worst-case running time); p. 1244, §2.3 (distributed computation of f, nodes s and r, R^G_ε(f)); p. 1248, §3.2 (execution φ_A(x,y), state σ_A(v,t,x,y))

import Mathlib

namespace DistVerif.Simulation

/-- A message of the B model: exactly `B` bits. Every directed edge carries one such message
in every round. -/
abbrev Msg (B : ℕ) : Type := Fin B → Bool

/-- A deterministic distributed algorithm in the B model (§1.1, p. 1237; §2.3, p. 1244) on a
network with vertex set `V`, bandwidth `B` and input strings of length `b`.
* `State` is the (arbitrary) local state space: nodes have unbounded computational power;
* `initS x`, `initR y` are the initial states of the two special nodes `s` and `r`, which
  receive `x` and `y`; `initO v` is the initial state of any other node `v` (no input);
* `send v w σ` is the `B`-bit message node `v` in state `σ` sends to its neighbour `w`;
* `step v σ m` is the new state of node `v` in state `σ` after receiving `m w` from each `w`;
* `outS`, `outR` read the outputs of `s` and `r` off their states. -/
structure DetAlg (V : Type) (B b : ℕ) where
  State : Type
  initS : (Fin b → Bool) → State
  initR : (Fin b → Bool) → State
  initO : V → State
  send : V → V → State → Msg B
  step : V → State → (V → Msg B) → State
  outS : State → Bool
  outR : State → Bool

namespace DetAlg

variable {V : Type} [DecidableEq V] {B b : ℕ}

/-- The execution `φ_A(x, y)` on the graph `G` with special nodes `s, r`:
`exec A G s r x y t v` is the state `σ_A(v, t, x, y)` of `v` at the end of round `t`.
Round `t + 1`: every node `w` sends to each neighbour `v` the message computed from its state
at the end of round `t`; a node receives a fixed all-`false` dummy from every non-neighbour. -/
def exec (A : DetAlg V B b) (G : SimpleGraph V) [DecidableRel G.Adj] (s r : V)
    (x y : Fin b → Bool) : ℕ → V → A.State
  | 0, v => if v = s then A.initS x else if v = r then A.initR y else A.initO v
  | t + 1, v => A.step v (exec A G s r x y t v)
      (fun w => if G.Adj w v then A.send w v (exec A G s r x y t w) else fun _ => false)

end DetAlg

/-- A public-coin randomized distributed algorithm (§2.1, p. 1243): a common random string
`ω` drawn from the distribution `μ` on `Ω` and seen by all nodes, and a deterministic B-model
algorithm for each value of `ω`. -/
structure PubAlg (V : Type) (B b : ℕ) where
  Ω : Type
  μ : PMF Ω
  alg : Ω → DetAlg V B b

/-- The public-coin algorithm `A`, run for `T` rounds on `G` with special nodes `s, r`, computes
`f` with `ε`-error (§2.1, §2.3): for every input pair `(x, y)`, the probability over the shared
random string that `s` or `r` fails to output `f(x, y)` after round `T` is at most `ε`. -/
def PubAlg.ComputesWithin {V : Type} [DecidableEq V] {B b : ℕ} (A : PubAlg V B b)
    (G : SimpleGraph V) [DecidableRel G.Adj] (s r : V) (T : ℕ)
    (f : (Fin b → Bool) → (Fin b → Bool) → Bool) (ε : ℝ) : Prop :=
  ∀ x y : Fin b → Bool,
    A.μ.toOuterMeasure
        {ω | ¬ ((A.alg ω).outS ((A.alg ω).exec G s r x y T s) = f x y ∧
                (A.alg ω).outR ((A.alg ω).exec G s r x y T r) = f x y)}
      ≤ ENNReal.ofReal ε

end DistVerif.Simulation


