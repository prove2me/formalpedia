-- Prove2me | Definitions.Def_GeoQAC_Supplement_InQAC0
-- name    : GeoQAC_Supplement_InQAC0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:20:13.880246+00:00
-- url     : https://prove2.me/theorems/abde3972-e147-416b-aea3-02def7d4ba61
-- title:
--   The decision classes $\mathrm{QAC}^0$ and 2D-$\mathrm{QAC}^0$
-- statement:
--   A family $L=(L_n)_{n}$ of Boolean functions $L_n:\{0,1\}^n\to\{0,1\}$ is in **$\mathrm{QAC}^0$** if there are a depth $d$ and a constant $k$ such that for every $n$ some depth-$d$ QAC circuit on at most $k(n+1)^k$ qubits computes $L_n$ with success probability at least $2/3$ on every input, ancillas starting in $|0\rangle$. It is in **2D-$\mathrm{QAC}^0$** if the same holds with $[w,h]$-2D-QAC circuits on $wh\le k(n+1)^k$ qubits.
--
--   Theorem 3.1 shows that the two classes coincide.
--
--   **Formalization Note** Circuit families are nonuniform. A depth-$d$ circuit on $q$ qubits has at most $dq$ multi-qubit gates (disjoint nonempty supports) and $(d+1)q$ one-qubit gates, so bounding the qubits bounds the gates. Depth exactly $d$ for every $n$ (empty layers allowed) is constant depth.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Definitions 2.2, 2.3, p.11

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_Supplement_ComputesWithProb

namespace GeoQAC.Supplement

open GeoQAC

/-!
# The decision classes `QAC⁰` and `2D-QAC⁰`

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), Definition 2.2, p.11: "A `QAC⁰` family
consists of constant-depth QAC circuits `{C_n}_{n≥1}` with polynomially many qubits and gates in the
input size `n`. As a decision class, `QAC⁰` denotes the languages computed by such families with
bounded worst-case error." Definition 2.3, p.11: "The classes `2D-QAC⁰` and `1D-QAC⁰` consist of
constant-depth, polynomial-size families in these geometries, with the same decision convention as
`QAC⁰`."

**Formalization Note.**
* A language is a family `L : (n : ℕ) → (Fin n → Bool) → Bool` of Boolean functions, one per input
  length. Bounded worst-case error is success probability at least `2/3` on every input (p.11),
  with `|0⟩` ancillas (p.10). Circuit families are nonuniform (p.10).
* Polynomially many qubits: at most `k·(n+1)^k`. A depth-`d` circuit on `q` qubits has at most
  `d·q` multi-qubit gates (disjoint nonempty supports) and `(d+1)·q` one-qubit gates, so a bound on
  the qubits is a bound on the gates.
* Depth exactly `d` for every `n` (empty layers allowed) is constant depth.
* Length `n = 0` is included; the constant functions of length `0` are in both classes.
-/

/-- `L ∈ QAC⁰` (Definition 2.2, p.11): constant depth `d`, at most `k(n+1)^k` qubits, success
probability at least `2/3` on every input. -/
def InQAC0 (L : (n : ℕ) → (Fin n → Bool) → Bool) : Prop :=
  ∃ d k : ℕ, ∀ n : ℕ, ∃ (q : ℕ) (C : QACCircuit (Fin q) d) (inp : Fin n ↪ Fin q) (out : Fin q),
    q ≤ k * (n + 1) ^ k ∧ ComputesWithProb (2 / 3) C inp out (L n)

/-- `L ∈ 2D-QAC⁰` (Definition 2.3, p.11): as `InQAC0`, with `[w, h]`-2D-QAC circuits on
`w·h ≤ k(n+1)^k` qubits. -/
def In2DQAC0 (L : (n : ℕ) → (Fin n → Bool) → Bool) : Prop :=
  ∃ d k : ℕ, ∀ n : ℕ, ∃ (w h : ℕ) (C : QACCircuit (Pos w h) d) (inp : Fin n ↪ Pos w h)
    (out : Pos w h), w * h ≤ k * (n + 1) ^ k ∧ C.Is2D ∧ ComputesWithProb (2 / 3) C inp out (L n)

end GeoQAC.Supplement


