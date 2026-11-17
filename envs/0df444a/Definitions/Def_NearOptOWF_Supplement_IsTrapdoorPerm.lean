-- Prove2me | Definitions.Def_NearOptOWF_Supplement_IsTrapdoorPerm
-- name    : NearOptOWF_Supplement_IsTrapdoorPerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:08:55.788871+00:00
-- url     : https://prove2.me/theorems/48bbf6f3-009e-4f84-9ce0-f261c9874e31
-- title:
--   Trapdoor permutation family
-- statement:
--   A sampleable family $\mathcal P$ of circuits $P:\{0,1\}^n\to\{0,1\}^n$, sampled from coins $\rho$, is a family of **trapdoor permutations** if
--
--   1. every sampled $P$ is a permutation of $\{0,1\}^n$: each $y\in\{0,1\}^n$ has exactly one pre-image in $\{0,1\}^n$;
--   2. a **trapdoor** $\mathrm{td}(\rho)$ is computed from $(1^n,\rho)$ in polynomial time, from the same coins that sample $P$;
--   3. a deterministic polynomial-time algorithm $\mathrm{Inv}$ inverts with the trapdoor: $\mathrm{Inv}(1^n, \mathrm{td}(\rho), P(x)) = x$ for every $x\in\{0,1\}^n$.
--
--   In the paper's construction $P = i\mathcal O(\mathrm{PRP}(k,\cdot))$ and the trapdoor is the key $k$.
--
--   **Formalization Note** Efficient sampling of $P$ itself is the base predicate `FunFamily.IsEfficient`, stated separately; polynomial time is the base single-machine model.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.3, Theorem 4.11 and Eq. (4), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_NearOptOWF_FunFamily
import Definitions.Def_LaconicBarrier_PolyTimeOn

namespace NearOptOWF.Supplement

open LaconicBarrier

/-- The sampled family `H` of circuits `{0,1}ⁿ → {0,1}ⁿ` is a family of **trapdoor permutations**
(Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.3, Theorem 4.11 and Eq. (4), p.20 (PDF p.22): "`P = {iO(PRP(k, ·)) : {0,1}ⁿ → {0,1}ⁿ}` …
The trapdoor of the permutation `iO(PRP(k, ·))` is the key `k`"):

1. every sampled circuit `samp n ρ` is a **permutation** of `{0,1}ⁿ`: each `y ∈ {0,1}ⁿ` has exactly one
   pre-image in `{0,1}ⁿ`;
2. a **trapdoor** `td n ρ` is computed from `(1ⁿ, ρ)` in polynomial time, from the same sampling coins
   `ρ` as the permutation;
3. a deterministic polynomial-time algorithm `Inv`, given `(1ⁿ, td n ρ, y)` for `y ∈ {0,1}ⁿ`, returns the
   pre-image: `Inv(1ⁿ, td n ρ, samp n ρ (x)) = x` for every `x ∈ {0,1}ⁿ`.

**Formalization Note** Efficient sampling of the permutation itself (polynomially many coins, `n`
output wires, polynomial-time description) is the base `FunFamily.IsEfficient`, stated separately.
Polynomial time is the base machine model `LaconicBarrier.PolyTimeOn` (one uniform machine). -/
def IsTrapdoorPerm (H : FunFamily (fun n => n)) : Prop :=
  (∀ (n : ℕ) (ρ : Fin (H.coins n) → Bool) (y : List Bool), y.length = n →
    ∃! x : List Bool, x.length = n ∧ (H.samp n ρ).eval x = y) ∧
  ∃ (td : (n : ℕ) → (Fin (H.coins n) → Bool) → List Bool) (Inv : List (List Bool) → List Bool),
    PolyTimeOn (ι := (n : ℕ) × (Fin (H.coins n) → Bool)) (fun i => [unary i.1, bits i.2])
      (fun i => td i.1 i.2) ∧
    PolyTimeOn (ι := {p : ((n : ℕ) × (Fin (H.coins n) → Bool)) × List Bool // p.2.length = p.1.1})
      (fun p => [unary p.1.1.1, td p.1.1.1 p.1.1.2, p.1.2])
      (fun p => Inv [unary p.1.1.1, td p.1.1.1 p.1.1.2, p.1.2]) ∧
    ∀ (n : ℕ) (ρ : Fin (H.coins n) → Bool) (x : List Bool), x.length = n →
      Inv [unary n, td n ρ, (H.samp n ρ).eval x] = x

end NearOptOWF.Supplement


