-- Prove2me | Definitions.Def_TargetedSamplers_IsSufficientlyUniform
-- name    : TargetedSamplers_IsSufficientlyUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:06:32.07452+00:00
-- url     : https://prove2.me/theorems/29885b52-f07b-4dc2-8412-b5b6f8796b80
-- title:
--   Sufficiently uniform circuit families (Definition 4.17)
-- statement:
--   Let $d,T,\ell:\mathbb N\to\mathbb N$ be time-constructible, with $T(n)$ always a power of $2$. A family $\{C_n\}$ is a **sufficiently uniform circuit family of width $T(n)$ and depth $d(n)$** (and output length $\ell(n)$) if:
--
--   1. **Circuit structure.** $C_n$ is a well-formed layered circuit with $d(n)+1$ layers of exactly $T(n)$ gates and $\ell(n)$ outputs.
--   2. **Uniformly printing the circuit.** One program, given $1^n$, prints the adjacency list $(i,g,b)\mapsto\mathrm{OUT}_i(g,b)$, $i\in[d]$, in time $\tilde O(d\cdot T)$.
--   3. **Uniformly deciding connectivity.** One program decides in time $\mathrm{polylog}(T)$, given $i,g,b,g'$ and $n$, whether $\mathrm{OUT}_i(g,b)=g'$.
--
--   **Formalization Note** Footnote 29 defines the direct connection language by in-edges ("the $p$th gate feeding into $G$ is $a$"). The proof queries it as $\langle g,g',b,1^n\rangle$ for $\mathrm{OUT}_i(g,b)=g'$ (p.33), so item 3 is read as the out-edge relation, with the layer in the gate label and $n$ in binary. $\tilde O(\cdot)$ is $\mathrm{budget}$ and $\mathrm{polylog}(T)$ is $K(\log_2T+1)^k$; the constants belong to the family.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 4.17 and footnote 29, p.28 (pdf p.30)

import Mathlib
import Definitions.Def_TargetedSamplers_LayeredCircuit
import Definitions.Def_TargetedSamplers_TimeConstructible

namespace TargetedSamplers

/-- Sufficiently uniform circuit families (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027
submission, manuscript sha256 599d0a59…, Definition 4.17, p.28). Let `d, T, ℓ : ℕ → ℕ` be
time-constructible, `T(n)` always a power of 2. `C = {C_n : {0,1}ⁿ → {0,1}^{ℓ(n)}}` is a
sufficiently uniform circuit family of width `T(n)` and depth `d(n)` if:

1. *Circuit structure.* `C_n` has `d(n) + 1` layers of exactly `T(n)` gates, the first layer gives
   access to all literals, later gates are fan-in-2 NAND gates, and the first `ℓ(n)` gates of layer
   `d + 1` are the outputs (`LayeredCircuit.WellFormed`).
2. *Uniformly printing the circuit.* One program prints, on input `1ⁿ`, the adjacency list
   `(i, g, b) ↦ OUTᵢ(g, b)`, `i ∈ [d]`, in time `Õ(d · T)`.
3. *Uniformly deciding connectivity.* One program decides, in time `polylog(T)`, whether
   `OUTᵢ(g, b) = g′`, given `i, g, b, g′` and `n` in binary.

**Formalization Note** Footnote 29 defines the direct connection language by in-edges ("the `p`th
gate feeding into `G` is `a`"), but the proof (p.33) queries it as `⟨g, g′, b, 1ⁿ⟩` for
`OUTᵢ(g, b) = g′`; item 3 is read as the out-edge relation, with the layer in the gate label and `n`
in binary. `Õ(d·T)` and the input `1ⁿ` use `budget`; `polylog(T)` is `K · (log₂ T + 1)^k`. The
constants `K, k` belong to the family. -/
def IsSufficientlyUniform (F : (n : ℕ) → LayeredCircuit n) (d T ℓ : ℕ → ℕ) : Prop :=
  TimeConstructible d ∧ TimeConstructible T ∧ TimeConstructible ℓ ∧
  (∀ n, (∃ e : ℕ, T n = 2 ^ e) ∧ (F n).width = T n ∧ (F n).depth = d n ∧ (F n).outLen = ℓ n ∧
    (F n).WellFormed) ∧
  (∃ (P : Program) (K k : ℕ), ∀ n,
    P.RunsIn (Tapes.ofInput (List.replicate n true)) (budget K k (d n * T n) n)
      (some (F n).adjEncoding)) ∧
  (∃ (D : Program) (K k : ℕ), ∀ n i, 1 ≤ i → i ≤ d n → ∀ (g g' : Fin (F n).width) (b : Bool),
    D.RunsIn (Tapes.ofInput (encInput [i, g, b.toNat, g', n] []))
      (K * (Nat.log 2 (T n) + 1) ^ k) (some [decide ((F n).out i g b = g')]))

end TargetedSamplers


