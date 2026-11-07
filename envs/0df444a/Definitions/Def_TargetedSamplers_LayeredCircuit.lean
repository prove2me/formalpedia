-- Prove2me | Definitions.Def_TargetedSamplers_LayeredCircuit
-- name    : TargetedSamplers_LayeredCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:45.816821+00:00
-- url     : https://prove2.me/theorems/e2adbe22-79f7-47bb-bb19-3641e6366077
-- title:
--   Layered NAND circuits with literal input layer
-- statement:
--   A **layered circuit** on $n$ inputs has layers $1,\dots,d+1$, each with exactly $T$ gates numbered $0,\dots,T-1$.
--
--   - **Layer 1** holds the literals: gate $g<n$ is $x_g$, gate $n+g$ ($g<n$) is $\neg x_g$, and the remaining gates hold the constant $0$.
--   - **Wiring.** For each layer $i\in[d]$, every gate $g$ of layer $i$ has two out-edges, labelled $b\in\{0,1\}$, to the gates $\mathrm{OUT}_i(g,b)$ of layer $i+1$.
--   - **Gates.** All gates of layers $2,\dots,d+1$ are NAND gates.
--   - **Outputs.** The first $\ell$ gates of layer $d+1$ are the outputs.
--
--   The circuit is **well formed** if $2n\le T$, every gate of layers $2,\dots,d+1$ has fan-in exactly $2$ (exactly two labelled out-edges point to it), and $\ell\le T$. The value of a gate and the output $C_n(x)\in\{0,1\}^\ell$ are defined layer by layer. The **adjacency list** is the bit string listing $\mathrm{OUT}_i(g,b)$ for $i\in[d]$, $g<T$, $b\in\{0,1\}$, each in $\log_2T$ bits. A family $\{C_n\}$ **computes** $f:\{0,1\}^*\to\{0,1\}^*$ if $f(x)=C_{|x|}(x)$ for every $x$.
--
--   **Formalization Note** Definition 4.17 says the first layer "provides access to all literals (specifically, inputs $x_1,\dots,x_n$ and their negations $\neg x_1,\dots,\neg x_n$)" and has exactly $T$ gates. The literals are laid out in this order and padded with $0$, as the proof of Theorem 4.23 pads layer 1 with $0$ (p.32). A fixed layout is what lets the input layer of the bootstrapping system be computed in time $O(\log T)$. Gates and inputs are numbered from $0$.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 4.17, p.28 (pdf p.30)

import Mathlib
import Definitions.Def_TargetedSamplers_encInput

namespace TargetedSamplers

/-- A layered circuit on `n` inputs (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027
submission, manuscript sha256 599d0a59…, Definition 4.17, p.28): layers `1, …, depth + 1`, each with
exactly `width` gates numbered `0, …, width − 1`. Layer 1 provides the literals: gate `g < n` is
`x_g`, gate `n + g` (`g < n`) is `¬x_g`, and the remaining gates are the constant `0`. For a layer
`i ∈ [depth]`, the gate `g` of layer `i` has two out-edges, labelled `b ∈ {0,1}`, to the gates
`out i g b = OUTᵢ(g, b)` of layer `i + 1`. Gates of layers `2, …, depth + 1` are NAND gates. The first
`outLen` gates of layer `depth + 1` are the outputs.

**Formalization Note** The paper says the first layer "provides access to all literals
(specifically, inputs x₁, …, xₙ and their negations ¬x₁, …, ¬xₙ)" and has exactly `width` gates. The
literals are laid out in this order and the remaining `width − 2n` gates hold `0`, as the proof pads
layer 1 with `0` (p.32). A fixed layout is what lets an input-layer algorithm run in time `O(log T)`
(Theorem 4.23, item 1). Gates are numbered from `0`, inputs `x₀, …, x_{n−1}`. -/
structure LayeredCircuit (n : ℕ) where
  width : ℕ
  depth : ℕ
  outLen : ℕ
  out : ℕ → Fin width → Bool → Fin width

namespace LayeredCircuit

variable {n : ℕ}

/-- The circuit-structure conditions of Definition 4.17: the `2n` literals fit in layer 1
(`2n ≤ width`); every gate of layers `2, …, depth + 1` has fan-in exactly 2 (exactly two labelled out-edges
of the previous layer point to it; fan-out 2 is built into `out`); and `outLen ≤ width`. -/
def WellFormed (c : LayeredCircuit n) : Prop :=
  2 * n ≤ c.width ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ c.depth → ∀ g' : Fin c.width,
    (Finset.univ.filter (fun e : Fin c.width × Bool => c.out i e.1 e.2 = g')).card = 2) ∧
  c.outLen ≤ c.width

open Classical in
/-- The value of gate `g` of layer `i` on input `x`. A NAND gate of layer `i + 1` outputs `0` iff
both its in-edges carry `1`, i.e. it outputs `1` iff some in-edge carries `0` (with fan-in 2 this is
NAND). Layer `0` does not exist and is set to `0`. -/
noncomputable def value (c : LayeredCircuit n) (x : Fin n → Bool) : ℕ → Fin c.width → Bool
  | 0 => fun _ => false
  | 1 => fun g =>
      if h : (g : ℕ) < n then x ⟨g, h⟩
      else if h' : (g : ℕ) < 2 * n then !x ⟨g - n, by omega⟩
      else false
  | i + 2 => fun g' =>
      decide (∃ g : Fin c.width, ∃ b : Bool, c.out (i + 1) g b = g' ∧ c.value x (i + 1) g = false)

/-- The output string `C_n(x) ∈ {0,1}^{outLen}`: the values of the first `outLen` gates of layer
`depth + 1`. -/
noncomputable def eval (c : LayeredCircuit n) (x : Fin n → Bool) : List Bool :=
  List.ofFn (fun j : Fin c.outLen =>
    if h : (j : ℕ) < c.width then c.value x (c.depth + 1) ⟨j, h⟩ else false)

/-- The adjacency list of the circuit as a bit string: for `i = 1, …, depth`, `g = 0, …, width − 1`,
`b = 0, 1`, the gate `OUTᵢ(g, b)` written in `log₂ width` bits (`bitsFixed`). -/
def adjEncoding (c : LayeredCircuit n) : List Bool :=
  (List.range c.depth).flatMap fun i =>
    (List.finRange c.width).flatMap fun g =>
      [false, true].flatMap fun b => bitsFixed (Nat.log 2 c.width) (c.out (i + 1) g b).val

end LayeredCircuit

/-- A circuit family `{C_n}_{n ∈ ℕ}` computes `f : {0,1}* → {0,1}*`: `f(x) = C_{|x|}(x)` for every
`x`. -/
def Computes (F : (n : ℕ) → LayeredCircuit n) (f : List Bool → List Bool) : Prop :=
  ∀ x : List Bool, f x = (F x.length).eval (toVec x)

end TargetedSamplers


