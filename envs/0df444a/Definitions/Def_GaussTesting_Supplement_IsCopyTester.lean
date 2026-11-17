-- Prove2me | Definitions.Def_GaussTesting_Supplement_IsCopyTester
-- name    : GaussTesting_Supplement_IsCopyTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:26:34.450543+00:00
-- url     : https://prove2.me/theorems/22f436b0-5efb-497f-818e-52bd841d2dd0
-- title:
--   Definition 1.2 — general $t$-copy $(\varepsilon_1,\varepsilon_2,\delta)$-testers (any effect on $t$ copies)
-- statement:
--   Let $\mathcal H=\ell^2(\iota)$ be a Hilbert space, $\mathcal C\subseteq\mathcal H$ a class of pure states and $t\in\mathbb N$. A **$t$-copy $(\varepsilon_1,\varepsilon_2,\delta)$-tester** for $\mathcal C$ is a two-outcome measurement $\{M,\,I-M\}$ on $\mathcal H^{\otimes t}$, i.e. an operator $M$ with
--
--   $$
--   0\preceq M\preceq I,
--   $$
--
--   accepting on the outcome $M$, such that for every unit vector $|\psi\rangle\in\mathcal H$, with acceptance probability $\Pr[\mathrm{ACCEPT}]=\langle\psi^{\otimes t}|M|\psi^{\otimes t}\rangle$:
--
--   1. if $\mathrm{dist}(\psi,\mathcal C)\le\varepsilon_1$, then $\Pr[\mathrm{ACCEPT}]\ge1-\delta$;
--   2. if $\mathrm{dist}(\psi,\mathcal C)\ge\varepsilon_2$, then $\Pr[\mathrm{ACCEPT}]\le\delta$.
--
--   Here $\mathrm{dist}(\psi,\mathcal C)=\inf_{\phi\in\mathcal C}\sqrt{1-|\langle\phi|\psi\rangle|^2}$ is the trace distance to the class. Every quantum algorithm that receives $|\psi\rangle^{\otimes t}$ and outputs ACCEPT or REJECT (with ancillas, intermediate measurements and adaptivity) accepts with probability $\langle\psi^{\otimes t}|M|\psi^{\otimes t}\rangle$ for one such $M$, so this is the paper's notion of a tester in full generality. Lower bounds on the number of copies quantify over these testers.
--
--   **Formalization Note** The auxiliary function `copyAccept M ψ` is $\mathrm{Re}\langle\psi^{\otimes t},M\psi^{\otimes t}\rangle$, with $\psi^{\otimes t}$ the published `GaussTesting.tpow`. The positivity conditions on $M$ are part of the predicate. This differs from the published `GaussTesting.IsTester`, which covers only block testers (one $k$-copy effect repeated in rounds).
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Definition 1.2, p.4; Remark 1.3, p.5; proof of Proposition 9.1, eq. (9.2), p.75

import Definitions.Def_GaussTesting_tpow
import Definitions.Def_GaussTesting_distTo

namespace GaussTesting

namespace Supplement

/-- The probability that the two-outcome measurement `{M, I − M}` on `ℋ^{⊗t}` returns the outcome `M`
on the input `|ψ⟩^{⊗t}`: `tr(M ψ^{⊗t}) = ⟨ψ^{⊗t}| M |ψ^{⊗t}⟩`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian
states*, arXiv:2609.39113 (sha256 6683e57b…), Definition 1.2, p.4; proof of Proposition 9.1, eq. (9.2),
p.75 ("Let `{M, I − M}` be any POVM on `N` copies").

**Formalization Note.** `inner ℂ` is conjugate-linear in its first argument, so this is
`Re ⟨ψ^{⊗t}, M ψ^{⊗t}⟩`; for an effect `M` the inner product is real. -/
noncomputable def copyAccept {ι : Type*} {t : ℕ} (M : Ell2 (Fin t → ι) →L[ℂ] Ell2 (Fin t → ι))
    (ψ : Ell2 ι) : ℝ :=
  (inner ℂ (tpow t ψ) (M (tpow t ψ))).re

/-- A general `t`-copy `(ε₁, ε₂, δ)`-tester for the class `𝒞`: an effect `M` on `ℋ^{⊗t}`
(`0 ≤ M ≤ I`, outcome `M` = ACCEPT) such that for every pure state `|ψ⟩`,
1. if `dist(ψ, 𝒞) ≤ ε₁` then `Pr[ACCEPT on |ψ⟩^{⊗t}] ≥ 1 − δ`, and
2. if `dist(ψ, 𝒞) ≥ ε₂` then `Pr[ACCEPT on |ψ⟩^{⊗t}] ≤ δ`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian
states*, arXiv:2609.39113 (sha256 6683e57b…), Definition 1.2, p.4 ("a `t`-copy `(ε₁, ε₂, δ)`-tester for
`𝒞` is an algorithm `A : Sym^t(ℋ) → {ACCEPT, REJECT}` such that for all `|ψ⟩ ∈ ℋ` …"), Remark 1.3, p.5.

**Formalization Note.**
* Any quantum algorithm with a binary output that is run on `|ψ⟩^{⊗t}`, with ancillas, adaptive
  intermediate measurements and classical randomness, accepts with probability `tr(M ψ^{⊗t})` for one
  effect `M` on `ℋ^{⊗t}` (Naimark/Stinespring dilation); conversely every effect is realized by such an
  algorithm. An effect on `Sym^t(ℋ)` extends to `ℋ^{⊗t}` by `Π_sym M Π_sym`, and an effect on `ℋ^{⊗t}`
  compresses to `Sym^t(ℋ)` with the same acceptance probabilities on `ψ^{⊗t} ∈ Sym^t(ℋ)`, so this is
  exactly Definition 1.2.
* This is not the published `GaussTesting.IsTester`, which is restricted to block testers (one `k`-copy
  effect repeated in rounds); lower bounds quantify over every tester.
* "For all `|ψ⟩ ∈ ℋ`" ranges over all unit vectors of the whole space; `ℋ^{⊗t}` is `ℓ²(Fin t → ι)`.
  The range conditions on `ε₁, ε₂, δ` are hypotheses of the theorems. -/
def IsCopyTester {ι : Type*} (C : Set (Ell2 ι)) (t : ℕ)
    (M : Ell2 (Fin t → ι) →L[ℂ] Ell2 (Fin t → ι)) (ε₁ ε₂ δ : ℝ) : Prop :=
  M.IsPositive ∧ (1 - M).IsPositive ∧
    ∀ ψ : Ell2 ι, ‖ψ‖ = 1 →
      (distTo ψ C ≤ ε₁ → 1 - δ ≤ copyAccept M ψ) ∧ (ε₂ ≤ distTo ψ C → copyAccept M ψ ≤ δ)

end Supplement

end GaussTesting


