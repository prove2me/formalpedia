-- Prove2me | Definitions.Def_FermiHubbardMix_ptr
-- name    : FermiHubbardMix_ptr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:51.045162+00:00
-- url     : https://prove2.me/theorems/88188007-5350-45b5-9841-b2a70971f42f
-- title:
--   Fermionic partial trace $\operatorname{tr}_S$
-- statement:
--   Let $S\subseteq\Lambda$ and $d_S=2^{m|S|}$. Every operator $X$ has a unique expansion $X=\sum_{\mu,\nu\in F_S}P^S_{\mu\nu}X^{(S)}_{\mu\nu}$ with $X^{(S)}_{\mu\nu}\in\mathfrak A_{S^c}$, and the **unnormalized fermionic partial trace** is $\operatorname{tr}_S(X)=\sum_\mu X^{(S)}_{\mu\mu}\in\mathfrak A_{S^c}$ (Definition 12.1). It is characterized (eqs. (14)–(15)) as the unique $Y\in\mathfrak A_{S^c}$ such that
--   $$
--   \operatorname{tr}(ZY)=d_S\operatorname{tr}(ZX)\qquad\text{for every }Z\in\mathfrak A_{S^c}.
--   $$
--   In particular $\operatorname{tr}_\emptyset(X)=X$ and $\operatorname{tr}_\Lambda(X)=\operatorname{tr}(X)\,I$.
--
--   The partial trace defines transport plans and the Wasserstein norm, and the hypotheses "$\operatorname{tr}_j(X)=0$" of Section 12.
--
--   **Formalization Note** The definition used is the characterization above (the unique $Y$ exists; uniqueness follows by testing with $Z=D^\dagger$, as on p.54). The fallback value for the case "no unique $Y$" never occurs.
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Definition 12.1, p.53; eqs. (14)–(15), pp.53–54

import Mathlib
import Definitions.Def_FermiHubbardMix_localAlg
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

open scoped Classical in
/-- **Definition 12.1 (Fermionic partial trace over a region)** (arXiv:2604.08408, held version
sha256 055b8f8f…, p.53): the unnormalized fermionic partial trace `tr_S : 𝔄_Λ → 𝔄_{S^c}`.

**Formalization Note** The paper defines `tr_S(X) = ∑_µ X^{(S)}_{µµ}` through the unique expansion
`X = ∑_{µν} P^S_{µν} X^{(S)}_{µν}` with `X^{(S)}_{µν} ∈ 𝔄_{S^c}`, and shows (eqs. (14)–(15), pp.53–54)
that `tr_S(X)` is the unique `Y ∈ 𝔄_{S^c}` with `tr(Z Y) = d_S tr(Z X)` for every `Z ∈ 𝔄_{S^c}`,
where `d_S = 2^{m|S|}` (uniqueness: test against `Z = D†`). This module defines `tr_S(X)` as that
unique `Y`. Such a `Y` always exists and is unique (the trace form is nondegenerate on the
`*`-algebra `𝔄_{S^c}`), so the fallback value `0` is never used. -/
def ptr {Λ : Type*} {m N : ℕ} (ord : Λ × Fin m ≃ Fin N) (S : Set Λ) (X : Op N) : Op N :=
  if h : ∃! Y : Op N, Y ∈ localAlg ord Sᶜ ∧
      ∀ Z ∈ localAlg ord Sᶜ, (Z * Y).trace = (2 : ℂ) ^ (m * Nat.card S) * (Z * X).trace
  then h.exists.choose else 0

end FermiHubbardMix


