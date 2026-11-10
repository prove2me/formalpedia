-- Prove2me | Definitions.Def_NearOptOWF_comp
-- name    : NearOptOWF_comp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:21.954173+00:00
-- url     : https://prove2.me/theorems/921626d9-96b0-402d-b0d0-f9c11cbfd893
-- title:
--   Composed circuit $g \circ h$
-- statement:
--   For circuits $h : \{0,1\}^n \to \{0,1\}^N$ and $g : \{0,1\}^N \to \{0,1\}^m$, the circuit $g \circ h$ consists of the gates of $h$, one copy gate for each output wire of $h$, and the gates of $g$ reading those copies. It computes $x \mapsto g(h(x))$ and has size about $|h| + N + |g|$.
--
--   It is the circuit obfuscated in the hybrid family $\mathcal H' = \{i\mathcal O(G \circ H)\}$ and in the pre-image sampler $A(g, y)$, which runs $A^*(i\mathcal O(g \circ H), y)$.
--
--   **Formalization Note** When $h$ does not have exactly $N$ output wires the construction is still a circuit but not the composition; the mission only composes $g$ with circuits $H$ that have $N = 10n$ outputs.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.2, p.14 (PDF p.16); Claim 4.7, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_NearOptOWF_mkMCircuit

namespace NearOptOWF

open LaconicBarrier

/-- The **composed circuit** `g ∘ h` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.2, p.14 (PDF p.16): "`H′ = {iO(G ◦ H)}`"; Claim 4.7,
p.15 (PDF p.17): "`iO(g ◦ H)`"): the gates of `h`, then one copy gate per output wire of `h`, then
the gates of `g` with its input wires redirected to the copies; the outputs are those of `g`.

**Formalization Note** When `h` has exactly `N` output wires, `(g ∘ h)(x) = g(h(x))` on every
`x ∈ {0,1}ⁿ`, and the size is `|h| + N + |g|` up to the output wires. Otherwise the composition is
still a circuit (built by `mkMCircuit`), and the mission never uses it then. -/
def comp {n N : ℕ} (g : MCircuit N) (h : MCircuit n) : MCircuit n :=
  let off := n + h.base.gates.length
  let L := h.outs.length
  let rel : ℕ → ℕ := fun w => if w < N then off + w else off + L + (w - N)
  let shift : KarpLiptonOM.Gate → KarpLiptonOM.Gate := fun gt =>
    match gt with
    | .const b => .const b
    | .not i => .not (rel i)
    | .and i j => .and (rel i) (rel j)
    | .or i j => .or (rel i) (rel j)
  mkMCircuit n (h.base.gates ++ h.outs.map (fun o => KarpLiptonOM.Gate.or o o) ++
    g.base.gates.map shift) (g.outs.map rel)

end NearOptOWF


