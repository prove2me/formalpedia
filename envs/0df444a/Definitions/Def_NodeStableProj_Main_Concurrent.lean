-- Prove2me | Definitions.Def_NodeStableProj_Main_Concurrent
-- name    : NodeStableProj_Main_Concurrent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:57:24.827339+00:00
-- url     : https://prove2.me/theorems/d4549169-1fd3-402f-bbd3-94d2b760ffd8
-- title:
--   Interactive mechanisms, concurrent s-sparse parallel composition, continual-release DP with adaptive inputs, noninteractive composition parameters, and the SVT detector mechanism
-- statement:
--   Every party draws its private randomness from its own **uniform tape**, an i.i.d. sequence of uniform $[0,1]$ reals; tapes of different parties are independent.
--
--   An **interactive mechanism** $\mathcal M$ with inputs in $X$ and outputs in $Y$ returns, after receiving inputs $x_1,\dots,x_t$, an output that is a function of its tape and $(x_1,\dots,x_t)$ (a stateful randomized process with private randomness). An **adversary** $\mathcal A$ running for a predetermined number $T$ of steps chooses at step $i$, from its tape and the outputs seen so far, a tuple $(m_i[0],m_i[1],j_i)$, and at the end outputs a value in a space $Z$. The **identifier** $\mathcal I[b]$ forwards $m_i[b]$ to mechanism $\mathcal M_{j_i}$, whose output goes to the adversary. $\mathcal A*\mathcal I[b]*\{\mathcal M_j\}$ is the law of the adversary's output.
--
--   $\mathcal A,\mathcal I$ **define a concurrent $s$-sparse composition** of $\{\mathcal M_j\}$ if the adversary's output is a random variable for both bits and, in every execution, at most $s$ steps have $m_i[0]\ne m_i[1]$ and each mechanism receives at most one such differing pair.
--
--   $\mathcal M$ is **$(\tilde\varepsilon,0)$-differentially private in the continual-release model with adaptive inputs** if for every adaptive adversary, with any output space, whose two input streams differ in at most one update (a $1$-sparse composition with the single mechanism $\mathcal M$), the laws of its output under $b=0$ and $b=1$ are $(\tilde\varepsilon,0)$-indistinguishable.
--
--   $(\varepsilon,\delta)$ are **valid for the noninteractive composition of $s$ $(\tilde\varepsilon,0)$-DP mechanisms** if for all probability laws $P_i,Q_i$ ($i<s$) on arbitrary measurable spaces with $P_i\approx_{\tilde\varepsilon,0}Q_i$, the product laws satisfy $\bigotimes_iP_i\approx_{\varepsilon,\delta}\bigotimes_iQ_i$.
--
--   The **SVT detector mechanism** with threshold $\tau$ and parameter $\tilde\varepsilon$ takes increments $b\in[0,1]$ and outputs its flag after each increment (Algorithm 2), with $\eta$ and $\xi_\ell$ obtained from its tape by inverting the distribution function of $\mathrm{Lap}(b)$: $b\ln(2u)$ for $u<1/2$, $-b\ln(2(1-u))$ for $u\ge1/2$.
--
--   **Formalization Note.** Tapes are `ℕ → unitInterval` with `Measure.infinitePi volume`. All mechanisms of a family share the types $X$, $Y$ (a heterogeneous family is coded with sum types). The adversary's output map must be measurable for $\mathcal A*\mathcal I[b]*\{\mathcal M_j\}$ to be a random variable; this is part of `IsSparseComposition`, and the continual-release DP quantifies over such adversaries.
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), pp. 15–16, §3.3.1; p. 13 Algorithm 2 and §3.1; p. 16 Proposition 3.7

import Mathlib
import Definitions.Def_PFRelease_Indist

open MeasureTheory

namespace NodeStableProj.Main

/-!
# Interactive mechanisms, concurrent `s`-sparse parallel composition, continual-release DP

Aden-Ali, Sealfon, Smith, Steinke, Ullman, *Node Differential Privacy via Node-Stable Graph
Projections*, STOC 2027 submission (manuscript sha256 42f18565…), pp. 15–16 (PDF 17–18), §3.3.1;
p. 13 (PDF 15) Algorithm 2 and §3.1.

**Formalization Note.**
* Randomness. Every party draws its private randomness from its own *uniform tape*
  `ℕ → [0, 1]` with the product of uniform laws (`tapeLaw`); tapes of different parties are
  independent. Any randomness a stateful mechanism or adversary may use on a standard Borel
  space is a measurable function of such a tape.
* An interactive mechanism `M` with inputs in `X` and outputs in `Y` is a map `resp`: on its tape
  `ω` and the list of inputs it has received so far (oldest first, current last), it returns its
  current output. This is a stateful randomized process with private randomness and state: its
  state after `t` inputs is a function of its tape and its first `t` inputs.
* An adversary with `T` steps (the predetermined number of steps) chooses, from its tape and the
  outputs seen so far, the next tuple `(m[0], m[1], j)`; at the end it outputs
  `out ωA (outputs) ∈ Z`. The identifier `I[b]` forwards `m[b]` to mechanism `j`, whose output is
  returned to the adversary. All mechanisms share the input type `X` and output type `Y` (a
  family with different types is coded with sum types).
* `A ∗ I[b] ∗ {M_j}` is the law of the adversary's output under the product of all tape laws
  (`compositionLaw`). For it to be a random variable the output map must be measurable; this is
  part of what it means that `A, I` *define* a composition (`IsSparseComposition`).
* `s`-sparse: in **every** execution (both bits, every tape) at most `s` steps have
  `m[0] ≠ m[1]`, and every mechanism receives at most one such differing pair.
* `(ε̃, 0)`-DP in the continual-release model with adaptive inputs: for every adaptive adversary
  sending pairs of input streams that differ in at most one update, the laws of its output under
  `b = 0` and `b = 1` are `(ε̃, 0)`-indistinguishable. This is the `1`-sparse composition with a
  single mechanism (`J = Unit`), with an arbitrary output space `Z` for the adversary.
* The SVT detector of Algorithm 2 as such a mechanism: inputs `b ∈ [0, 1]` (`unitInterval`), output
  the flag after each `increment`; its noises are read from its tape by inversion of the Laplace
  distribution function (`lapInv`).
-/

/-- The uniform tape law: independent uniform draws on `[0, 1]`, indexed by `ℕ`. -/
noncomputable def tapeLaw : Measure (ℕ → unitInterval) :=
  Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)

/-- A randomized interactive mechanism with inputs `X` and outputs `Y`. -/
structure Mechanism (X Y : Type) where
  /-- The output after receiving the inputs `xs` (oldest first), on private tape `ω`. -/
  resp : (ℕ → unitInterval) → List X → Y

/-- An adversary with message type `X`, mechanism indices `J`, mechanism outputs `Y` and final
output `Z`, running for the predetermined number of steps `T`. -/
structure Adversary (J X Y Z : Type) where
  /-- The number of steps. -/
  T : ℕ
  /-- The next tuple `(m[0], m[1], j)`, from the adversary's tape and the outputs seen so far. -/
  query : (ℕ → unitInterval) → List Y → X × X × J
  /-- The final output, from the adversary's tape and all outputs seen. -/
  out : (ℕ → unitInterval) → List Y → Z

/-- One recorded step of an execution: `(m[0], m[1], j, output)`. -/
abbrev Step (J X Y : Type) := X × X × J × Y

/-- The execution of `A ∗ I[b] ∗ {M_j}` for `t` steps on adversary tape `ωA` and mechanism tapes
`ωM`: the list of recorded steps, oldest first. At each step the adversary queries on the outputs
so far, `m[b]` is appended to the inputs of mechanism `j`, and `M_j` answers on its whole input
list. -/
def execution {J X Y Z : Type} [DecidableEq J] (M : J → Mechanism X Y) (A : Adversary J X Y Z)
    (b : Bool) (ωA : ℕ → unitInterval) (ωM : J → ℕ → unitInterval) : ℕ → List (Step J X Y)
  | 0 => []
  | t + 1 =>
    let h := execution M A b ωA ωM t
    let q := A.query ωA (h.map fun r => r.2.2.2)
    let x := if b then q.2.1 else q.1
    let j := q.2.2
    let inputs := (h.filter fun r => decide (r.2.2.1 = j)).map
      (fun r => if b then r.2.1 else r.1)
    h ++ [(q.1, q.2.1, j, (M j).resp (ωM j) (inputs ++ [x]))]

/-- The adversary's output on one execution of `T` steps. -/
def compositionOutcome {J X Y Z : Type} [DecidableEq J] (M : J → Mechanism X Y)
    (A : Adversary J X Y Z) (b : Bool) (ω : (ℕ → unitInterval) × (J → ℕ → unitInterval)) : Z :=
  A.out ω.1 ((execution M A b ω.1 ω.2 A.T).map fun r => r.2.2.2)

/-- `A ∗ I[b] ∗ {M_j}`: the law of the adversary's output, all tapes independent and uniform. -/
noncomputable def compositionLaw {J X Y Z : Type} [DecidableEq J] [MeasurableSpace Z]
    (M : J → Mechanism X Y) (A : Adversary J X Y Z) (b : Bool) : Measure Z :=
  (tapeLaw.prod (Measure.infinitePi fun _ : J => tapeLaw)).map (compositionOutcome M A b)

open Classical in
/-- `A, I` define a concurrent `s`-sparse parallel composition of `{M_j}`: the output is a random
variable for both bits, and in every execution at most `s` steps carry a differing pair
`m[0] ≠ m[1]`, each mechanism being the recipient of at most one of them. (`X` need not have decidable
equality: the counts are taken classically.) -/
def IsSparseComposition {J X Y Z : Type} [DecidableEq J] [MeasurableSpace Z]
    (M : J → Mechanism X Y) (A : Adversary J X Y Z) (s : ℕ) : Prop :=
  (∀ b : Bool, Measurable (compositionOutcome M A b)) ∧
  ∀ (b : Bool) (ωA : ℕ → unitInterval) (ωM : J → ℕ → unitInterval),
    let h := execution M A b ωA ωM A.T
    (h.filter fun r => decide (r.1 ≠ r.2.1)).length ≤ s ∧
      ∀ j : J, (h.filter fun r => decide (r.1 ≠ r.2.1 ∧ r.2.2.1 = j)).length ≤ 1

/-- `M` is `(ε, 0)`-differentially private in the continual-release model with adaptive inputs:
for every output space `Z` and every adaptive adversary whose two input streams differ in at most
one update (a `1`-sparse composition with the single mechanism `M`), the laws of the adversary's
output under `b = 0` and `b = 1` are `(ε, 0)`-indistinguishable. -/
def IsContinualDP {X Y : Type} (M : Mechanism X Y) (ε : ℝ) : Prop :=
  ∀ (Z : Type) [MeasurableSpace Z] (A : Adversary Unit X Y Z),
    IsSparseComposition (fun _ => M) A 1 →
      PFRelease.Indist (compositionLaw (fun _ => M) A false)
        (compositionLaw (fun _ => M) A true) ε 0

/-- `(ε, δ)` are valid parameters for the standard noninteractive composition of `s` mechanisms
that are `(ε̃, 0)`-differentially private: for any `s` pairs of probability laws `P_i, Q_i`, on
any measurable spaces, with `P_i ≈_{ε̃,0} Q_i`, the product laws satisfy
`⊗ P_i ≈_{ε,δ} ⊗ Q_i`. -/
def NonInteractiveComposition (s : ℕ) (εt ε δ : ℝ) : Prop :=
  ∀ (Ω : Fin s → Type) [∀ i, MeasurableSpace (Ω i)] (P Q : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)],
    (∀ i, PFRelease.Indist (P i) (Q i) εt 0) →
      PFRelease.Indist (Measure.pi P) (Measure.pi Q) ε δ

/-- The inverse distribution function of `Lap(b)`: `b ln(2u)` for `u < 1/2` and
`−b ln(2(1 − u))` for `u ≥ 1/2`. For `u` uniform on `[0, 1]` its law is `Lap(b)`. -/
noncomputable def lapInv (b u : ℝ) : ℝ :=
  if u < 1 / 2 then b * Real.log (2 * u) else -(b * Real.log (2 * (1 - u)))

/-- The state `(count, flag)` of the SVT detector of Algorithm 2 with threshold `τ`, after the
increments `bs` (oldest first), with `η = lapInv (2/ε̃) (ω 0)` and the query noise of the `ℓ`-th
call `ξ_ℓ = lapInv (4/ε̃) (ω ℓ)`. -/
noncomputable def svtState (τ εt : ℝ) (ω : ℕ → unitInterval) (bs : List unitInterval) :
    ℝ × Bool :=
  (bs.zipIdx 1).foldl
    (fun (st : ℝ × Bool) (p : unitInterval × ℕ) =>
      if st.2 then st
      else
        let c := st.1 + (p.1 : ℝ)
        (c, decide (τ + lapInv (2 / εt) (ω 0) < c + lapInv (4 / εt) (ω p.2))))
    (0, false)

/-- The SVT detector mechanism (Algorithm 2) with threshold `τ` and parameter `ε̃`: inputs are
increments `b ∈ [0, 1]`, and after each increment it outputs its flag (`true` = `⊤`). -/
noncomputable def svtMechanism (τ εt : ℝ) : Mechanism unitInterval Bool where
  resp ω bs := (svtState τ εt ω bs).2

end NodeStableProj.Main


