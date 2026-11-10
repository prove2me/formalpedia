-- Prove2me | Definitions.Def_KoanaKPaths_Main_Inputs
-- name    : KoanaKPaths_Main_Inputs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:36:51.550194+00:00
-- url     : https://prove2.me/theorems/32fa7135-ca6f-4a84-af9b-8eafe10e7774
-- title:
--   Bit inputs of the counting algorithms, tolerance controls and the time budget
-- statement:
--   The algorithms of Theorems 1 and 2 read finite bit strings. A natural number is written with the self-delimiting binary code of the reused machine model, and lists carry their length.
--
--   1. A tolerance $x\in(0,1)$ is passed as its **control** $\operatorname{ctrl}(x)=\lceil\log_2(1/x)\rceil$, the unique positive integer $a$ with $2^{-a}\le x<2^{1-a}$.
--   2. The input of the path-counting algorithm is the vertex count $n$, the path size $k$, $\operatorname{ctrl}(\varepsilon)$, $\operatorname{ctrl}(\delta)$ and the list of arcs $(u,v)$, vertices numbered $0,\dots,n-1$.
--   3. A gate is written as a tag ($0$ constant, $1$ addition, $2$ right product) followed by its fields; a circuit is its output position followed by its list of gates. The input of the monomial-counting algorithm is the circuit followed by $\operatorname{ctrl}(\varepsilon)$ and $\operatorname{ctrl}(\delta)$.
--   4. The **time budget** for size parameter $s$ and controls $a,b$ is
--   $$B=K\cdot 2^k\cdot(1+k+s)^c\cdot 4^a\cdot(b+1),$$
--   with a constant $K$ and an exponent $c$ fixed before all inputs.
--
--   Since $4^a<4\varepsilon^{-2}$ and $b+1<2+\log_2(1/\delta)$, the budget is at most a constant multiple of $2^k(1+k+s)^c\,\varepsilon^{-2}(1+\log(1/\delta))$: it is an explicit form of the source's $O^*(2^k\varepsilon^{-2}\log(1/\delta))$, with the polynomial factor in $k$ and the input size made explicit.
--   The size parameter excludes the tolerance controls: it is the length of `circuitCode C` for circuits and $n$ plus the length of `graphCode n arcs` for graphs. The latter encodes only $n$ and the arc list. Thus no additional dependence on $\varepsilon$ or $\delta$ is hidden in the polynomial factor.
-- source:
--   Tomohiro Koana, STOC 2027 submission #953 (October 2026), p. 1 (PDF p. 2), Section 1 (meaning of O*); p. 5 (PDF p. 6), Section 3 preamble; p. 9 (PDF p. 10), Running time

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_KoanaKPaths_Main_Circuits

noncomputable section

namespace KoanaKPaths.Main

open HypergraphUnreliability.FPRAS

/-- The finite tolerance control of a real `x ∈ (0, 1)`: `ctrl x = ⌈log₂(1/x)⌉`, the unique
positive integer `a` with `2^{-a} ≤ x < 2^{1-a}`. A machine receives `ctrl ε` and `ctrl δ`, not
the real numbers themselves. -/
def ctrl (x : ℝ) : ℕ := ⌈Real.logb 2 x⁻¹⌉₊

/-- The graph encoding alone, without the parameter or tolerance controls. Its length is the
graph input size in the polynomial factor of the running-time bound. -/
def graphCode (n : ℕ) (arcs : List (Fin n × Fin n)) : List Bool :=
  natCode n ++ listCode (fun p : Fin n × Fin n => natCode p.1.val ++ natCode p.2.val) arcs

/-- The bit input of the path-counting algorithm: the vertex count `n`, the path size `k`, the
controls of `ε` and `δ`, and the arc list (each arc `(u, v)` as two self-delimiting binary
numbers, 0-based vertices), in the order given. -/
def graphInput (n : ℕ) (arcs : List (Fin n × Fin n)) (k : ℕ) (ε δ : ℝ) : List Bool :=
  natCode n ++ natCode k ++ natCode (ctrl ε) ++ natCode (ctrl δ) ++
    listCode (fun p : Fin n × Fin n => natCode p.1.val ++ natCode p.2.val) arcs

/-- Binary code of a gate: a tag (`0` constant, `1` addition, `2` right product) and its fields. -/
def gateCode : Gate → List Bool
  | .const b => natCode 0 ++ natCode (if b then 1 else 0)
  | .add g₁ g₂ => natCode 1 ++ natCode g₁ ++ natCode g₂
  | .mulVar g j => natCode 2 ++ natCode g ++ natCode j

/-- Binary code of a circuit: its output position, then its gate list. Its length is the encoding
size `L` of the circuit. -/
def circuitCode (C : Circuit) : List Bool :=
  natCode C.output ++ listCode gateCode C.gates

/-- The bit input of the monomial-counting algorithm: the circuit, then the controls of `ε`, `δ`. -/
def circuitInput (C : Circuit) (ε δ : ℝ) : List Bool :=
  circuitCode C ++ natCode (ctrl ε) ++ natCode (ctrl δ)

/-- The explicit form of `O*(2^k ε^{-2} log(1/δ))`: `K · 2^k · (1 + k + size)^c · 4^a · (b + 1)`
for the controls `a = ctrl ε`, `b = ctrl δ`, with a constant `K` and an exponent `c` fixed before
all inputs. The size is `circuitCode C`'s length, or `n + (graphCode n arcs).length`, independent
of the controls. Since `4^a < 4 ε^{-2}` and `b + 1 < 2 + log₂(1/δ)`, it is at most a constant times
`2^k (1 + k + size)^c ε^{-2} (1 + log(1/δ))`. -/
def timeBudget (K c k size a b : ℕ) : ℕ :=
  K * 2 ^ k * (1 + k + size) ^ c * 4 ^ a * (b + 1)

end KoanaKPaths.Main

end


