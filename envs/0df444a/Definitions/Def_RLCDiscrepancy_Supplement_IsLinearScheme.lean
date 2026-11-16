-- Prove2me | Definitions.Def_RLCDiscrepancy_Supplement_IsLinearScheme
-- name    : RLCDiscrepancy_Supplement_IsLinearScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:49:28.232438+00:00
-- url     : https://prove2.me/theorems/42a99df7-f3ae-4ca4-b410-eaa4e6838c64
-- title:
--   Linear secret sharing scheme with shares in $\mathbb F_q$ (Definition 6.2, $m=1$; corrected at $\alpha=\beta=0$)
-- statement:
--   A secret sharing scheme $(\mathrm{Share},\mathrm{Rec})$ with secrets and shares in $\mathbb F_q$ ($m=1$) is **linear** if
--
--   1. for every secret $s$, the share vector $\mathrm{Share}(s)$ is uniformly distributed over an affine subspace of $\mathbb F_q^n$;
--   2. if $S=\mathrm{Share}(s)$ and $S'=\mathrm{Share}(s')$ are produced by independent runs of $\mathrm{Share}$, then $\alpha S+\beta S'$ is identically distributed to $\mathrm{Share}(\alpha s+\beta s')$ for all $\alpha,\beta\in\mathbb F_q$ not both zero.
--
--   Section 6 studies linear ramp schemes with $m=1$ (p.46), and Theorem 6.5 asserts the existence of such a scheme.
--
--   **Formalization Note** Uniform coins on a finite $\Omega$; independent runs use coins uniform on $\Omega\times\Omega$. The printed third clause also covers $\alpha=\beta=0$, where it says the constant $0$ has the law of $\mathrm{Share}(0)$; that fails for every scheme with non-constant shares (for the Massey scheme $\mathrm{Share}(0)$ is uniform on the code), so the clause is required for $(\alpha,\beta)\neq(0,0)$, the minimal correction under which the Massey scheme of §6.3 is linear.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 6.2, p.45, and p.46

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_RLCDiscrepancy_Supplement_RampScheme

namespace RLCDiscrepancy.Supplement

open Classical in
/-- **Linear secret sharing scheme with m = 1** (Definition 6.2, with the restriction of p.46).
Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 6.2, p.45: "We say that a ramp secret sharing
scheme (Share, Rec) is linear if the following holds: • The Share procedure maps a secret s ∈ F_q to
shares S_i ∈ F^m_q for some integer m; • For every s ∈ F_q, the tuple Share(s) is uniformly distributed
over an affine subspace of (F^m_q)^n; • If S = (S_1, …, S_n) = Share(s) and S′ = (S′_1, …, S′_n) = Share(s′)
for any two secrets s, s′ ∈ F_q, then αS + βS′ is identically distributed to Share(αs + βs′), for any
α, β ∈ F_q." p.46: "We will be interested in linear ramp secret sharing schemes with m = 1, i.e., whose
secrets and shares are elements of F_q."

**Formalization Note.** m = 1 is built into `RampScheme F n Ω` (secrets and shares in `F`). "Uniformly
distributed over an affine subspace A" is: every `y` has probability `1/|A|` if `y ∈ A` and `0`
otherwise, under uniform coins on `Ω` (`PunctSketch.coinProb`). S and S′ come from two independent runs of
Share (coins `(ω, ω′)` uniform on `Ω × Ω`). **Correction:** the third clause is required for
`(α, β) ≠ (0, 0)` only. At α = β = 0 the printed clause says that the constant `0` has the law of
`Share(0)`, which fails for every scheme whose shares are not constant (for the Massey scheme `Share(0)` is
uniform on the code `C`), so as printed no scheme with a nontrivial share space is linear; with
`(α, β) ≠ (0, 0)` the Massey scheme of §6.3 is linear, as the paper intends. -/
def IsLinearScheme {F : Type*} [Field F] [Fintype F] {n : ℕ} {Ω : Type*} [Fintype Ω]
    (P : RampScheme F n Ω) : Prop :=
  (∀ s : F, ∃ A : AffineSubspace F (Fin n → F), ∀ y : Fin n → F,
      PunctSketch.coinProb (fun ω => P.share s ω = y) =
        if y ∈ A then 1 / ((Finset.univ.filter (fun x : Fin n → F => x ∈ A)).card : ℝ) else 0) ∧
  (∀ s s' α β : F, (α, β) ≠ (0, 0) → ∀ y : Fin n → F,
      PunctSketch.coinProb (fun p : Ω × Ω => α • P.share s p.1 + β • P.share s' p.2 = y) =
        PunctSketch.coinProb (fun ω => P.share (α * s + β * s') ω = y))

end RLCDiscrepancy.Supplement


