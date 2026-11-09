-- Prove2me | Definitions.Def_NoisyOWMPC_IsA8Family
-- name    : NoisyOWMPC_IsA8Family
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:45:34.882668+00:00
-- url     : https://prove2.me/theorems/d6831fae-a7b6-4562-9e22-d8ac487cb538
-- title:
--   Expander families as in Corollary A.8
-- statement:
--   A family $G(M,\ell,G)$ of layered graphs with $M$ layers is **as in Corollary A.8 for constants $(c,\gamma)$** if there are constants $K_1,K_2>0$, an exponent $e$ and a threshold $M_0$ such that
--   1. one deterministic polynomial-time machine computes the neighbors $\gamma_j(f)$ from $(1^M,1^\ell,1^G,j,f)$, and one computes $\mathrm{Rec}_G(\Lambda)$;
--   2. for every $M\ge M_0$ with $M+1$ a power of two and all integers $\ell,G$ with $1\le\ell\le M^c$ and $M^\gamma\le G\le M$, the graph is $(M\ell,G,M^e)$-list-recoverable, its seed length satisfies
--   $$K_1\sqrt G\log_2M\le\kappa\le K_2\sqrt G\log_2 M,$$
--   and it has at most $M^e$ labels.
--
--   The tests and the selector of §5.2 take "the layered … expander of Corollary A.8 with $(c,\gamma,r)=\dots$" as an ingredient; the mission's constructions take any family with these properties, and Corollary A.8 says one exists.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Corollary A.8, p.48; Constructions 5.6, 5.11, 5.17, pp.25–28

import Mathlib
import Definitions.Def_NoisyOWMPC_LayeredGraph
import Definitions.Def_LaconicBarrier_PolyTimeOn
import Definitions.Def_KarpLiptonOM_binW
import Definitions.Def_QAdvFew_PoQOracle_tup

namespace NoisyOWMPC

open LaconicBarrier KarpLiptonOM

/-- `Gr` is a **family of expanders as in Corollary A.8 for the constants `(c, γ)`** (Ishai, Lu,
Zafar, STOC 2027 submission (manuscript sha256 3a9569fa…), Corollary A.8, p.48): "Let `q = M + 1`
be a power of two, and let integer parameters `ℓ, G` satisfy `1 ≤ ℓ ≤ M^c`, `M^γ ≤ G ≤ M`. For all
sufficiently large `M`, there is an efficiently constructible layered `(Mℓ, G, L_out)`-list-
recoverable expander `G` with left vertices `{0,1}^κ`, right vertices `[M] × H`, and one neighbor in
each layer, where `κ = Θ(√G log M)`, `|H| = M^{O(1)}`, `L_out = M^{O(1)}`. Its recovery algorithm is
deterministic and runs in time polynomial in `M` for the fixed constants `c, γ`."

`Gr M ℓ G` is a layered graph with `M` layers; there are constants `K₁, K₂ > 0`, an exponent `e`
and a threshold `M₀` such that:
1. one deterministic polynomial-time machine computes the neighbor `γ_j(f)` from
   `(1^M, 1^ℓ, 1^G, j, f)`, and one computes the recovery list `Rec_G(Λ)` from `(1^M, 1^ℓ, 1^G, Λ)`
   (a right set given by its indicator vector over `[M] × H`);
2. for every `M ≥ M₀` with `M + 1` a power of two and all integers `ℓ, G` with `1 ≤ ℓ ≤ M^c` and
   `M^γ ≤ G ≤ M`, the graph `Gr M ℓ G` is `(Mℓ, G, M^e)`-list-recoverable,
   `K₁ √G log₂ M ≤ κ ≤ K₂ √G log₂ M`, and `|H| ≤ M^e`.

**Formalization Note** `Θ` and `O` hide constants depending only on `(c, γ)`; the recovery time is
polynomial in its input, whose length is `M · |H| = M^{O(1)}`. The constructions of the tests and
the selector take such a family as a parameter (Constructions 5.6, 5.11, 5.17: "the layered …
expander of Corollary A.8 with `(c, γ, r) = …`"); Corollary A.8 states that one exists. -/
def IsA8Family (Gr : (M ℓ G : ℕ) → LayeredGraph M) (c γ : ℝ) : Prop :=
  ∃ (K₁ K₂ : ℝ) (e M₀ : ℕ), 0 < K₁ ∧ 0 < K₂ ∧
    PolyTimeOn (ι := (z : ℕ × ℕ × ℕ) × Fin z.1 × (Fin (Gr z.1 z.2.1 z.2.2).κ → Bool))
      (fun w => [unary w.1.1, unary w.1.2.1, unary w.1.2.2, binW (Nat.size w.1.1) w.2.1.val,
        bits w.2.2])
      (fun w => binW (Nat.size (Gr w.1.1 w.1.2.1 w.1.2.2).h)
        ((Gr w.1.1 w.1.2.1 w.1.2.2).γ w.2.1 w.2.2).val) ∧
    PolyTimeOn (ι := (z : ℕ × ℕ × ℕ) × Finset (Fin z.1 × Fin (Gr z.1 z.2.1 z.2.2).h))
      (fun w => [unary w.1.1, unary w.1.2.1, unary w.1.2.2,
        List.ofFn fun p : Fin (w.1.1 * (Gr w.1.1 w.1.2.1 w.1.2.2).h) =>
          decide (finProdFinEquiv.symm p ∈ w.2)])
      (fun w => QAdvFew.PoQOracle.tup (((Gr w.1.1 w.1.2.1 w.1.2.2).recov w.2).map bits)) ∧
    ∀ M ≥ M₀, (∃ t : ℕ, M + 1 = 2 ^ t) → ∀ ℓ G : ℕ, 1 ≤ ℓ → (ℓ : ℝ) ≤ (M : ℝ) ^ c →
      (M : ℝ) ^ γ ≤ G → G ≤ M →
        (Gr M ℓ G).IsListRec (M * ℓ) G (M ^ e) ∧
        K₁ * Real.sqrt G * Real.logb 2 M ≤ ((Gr M ℓ G).κ : ℝ) ∧
        ((Gr M ℓ G).κ : ℝ) ≤ K₂ * Real.sqrt G * Real.logb 2 M ∧
        (Gr M ℓ G).h ≤ M ^ e

end NoisyOWMPC


