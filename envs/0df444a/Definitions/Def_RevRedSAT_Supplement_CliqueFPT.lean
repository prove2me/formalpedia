-- Prove2me | Definitions.Def_RevRedSAT_Supplement_CliqueFPT
-- name    : RevRedSAT_Supplement_CliqueFPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:55:44.204254+00:00
-- url     : https://prove2.me/theorems/10114153-d5ca-468c-bd17-bb1d4b84a7a4
-- title:
--   FPT $=$ W[1], read as fixed-parameter tractability of Clique
-- statement:
--   A function $g:\mathbb N\to\mathbb R$ is **effectively sublinear** if there is a computable $b:\mathbb N\to\mathbb N$ such that
--
--   $$g(k)\le k/a\quad\text{whenever } a\ge1 \text{ and } k\ge b(a)$$
--
--   (Theorems 5.5 and 6.18).
--
--   **CliqueFPT** states that there are a Turing machine with finite stack alphabets, a computable $f:\mathbb N\to\mathbb N$ and an exponent $c$ such that the machine decides Clique, on every code $w$ of a graph and a clique size $\ell$, within $f(\ell)\,|w|^c$ steps.
--
--   W[1] is the closure of Clique under FPT reductions, and FPT is closed under FPT reductions, so FPT $=$ W[1] holds exactly when Clique is fixed-parameter tractable. This is the conclusion of Theorems 5.5 and 6.18, whose proofs end by giving an FPT algorithm for Clique.
--
--   **Formalization Note** FPT is the strongly uniform class (computable $f$). Clique instances use the published Vertex Cover codes, the last number being $\ell$.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 5.5 and its proof, pp.37–38; Theorem 6.18 and its proof, pp.49–50; App. C.6, p.95 (Clique)

import Mathlib
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_VCInstance
import Definitions.Def_RevRedSAT_Supplement_DecideWithin
import Definitions.Def_RevRedSAT_Supplement_CVCValid

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **An effectively sublinear function** (Theorem 5.5, p.37: "effectiveness means that there is a
computable function b: N≥1 → N such that g(k) ≤ k/a whenever k ≥ b(a)"; Theorem 6.18, p.49: "given
any positive integer a, one can compute a threshold b(a) satisfying g(t) ≤ t/a for all t ≥ b(a)").
The values of `b` at `0` are irrelevant. -/
def EffectivelySublinear (g : ℕ → ℝ) : Prop :=
  ∃ b : ℕ → ℕ, Computable b ∧ ∀ a : ℕ, 1 ≤ a → ∀ k : ℕ, b a ≤ k → g k ≤ (k : ℝ) / a

/-- **FPT = W[1], read as: Clique is fixed-parameter tractable.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), proofs of Theorems 5.5 (p.37–38) and 6.18 (p.49–50): "We give an FPT algorithm for Clique. …
its W[1]-completeness proves the claim"; App. C.6, p.95 (Clique, parameter ℓ).

There are a machine `M` with finite alphabets, a computable `f : ℕ → ℕ` and an exponent `c` such
that `M` decides Clique (the published Vertex Cover codes `RevRedSAT.IsVCCode`, the last number
being `ℓ`) within `f(ℓ) · |w|^c` steps on every code `w`.

**Formalization Note** W[1] is the closure of Clique under FPT reductions (equivalent to the
weighted-circuit definition by the Downey–Fellows completeness theorem), and FPT is closed under FPT
reductions, so FPT = W[1] holds exactly when Clique is in FPT. FPT is the strongly uniform class
(computable `f`). -/
def CliqueFPT : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
    ∃ f : ℕ → ℕ, Computable f ∧ ∃ c : ℕ,
      DecideWithin M IsVCCode CliqueYes (fun I w => f I.k * w.length ^ c)

end RevRedSAT.Supplement


