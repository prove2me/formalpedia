-- Prove2me | Definitions.Def_TolProdTest_fC
-- name    : TolProdTest_fC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:28.722052+00:00
-- url     : https://prove2.me/theorems/d407bbf4-4e05-4942-9316-dfcfa13907f1
-- title:
--   Block-product fidelity $F_C(\rho)$ and $q$-block fidelity $F_q(\rho)$
-- statement:
--   Let $C$ be a coloring of the sites with colours in a finite set, with blocks $B_c=C^{-1}(c)$ and block spaces $\mathcal H_c=\bigotimes_{i\in B_c}\mathbb C^d$ (an empty block has $\mathcal H_c=\mathbb C$). The **block-product fidelity** is
--
--   $$
--   F_C(\rho)=\max_{|v_c\rangle\in\mathcal H_c,\ \||v_c\rangle\|_2=1}\ \langle v_1\otimes\cdots\otimes v_q|\,\rho\,|v_1\otimes\cdots\otimes v_q\rangle ,
--   $$
--
--   which allows entanglement inside each block but requires product structure across blocks. The **$q$-block fidelity** minimizes over colorings with $q$ colours:
--
--   $$
--   F_q(\rho)=\min_{C:[n]\to[q]}F_C(\rho).
--   $$
--
--   These are the intermediate quantities of the analysis: random coloring (Theorem 3.1) compares $F_q$ with $F_{\mathrm{prod}}$, and blockwise spectral projection (Theorem 3.4) bounds the test statistic by $F_q$.
--
--   **Formalization Note** The colour set is any finite type (colorings with more than $q$ colours occur in the proof of Lemma 3.3 (ii)); block vectors have basis `{i // C i = c} → Fin d`. $F_C$ is an `sSup` (attained), $F_q$ a finite `⨅` over `Fin n → Fin q`, which is the minimum for $q\ge1$; colours are 0-based.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eqs. (22)–(23), p.9

import Mathlib
import Definitions.Def_TolProdTest_fprod

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- The block-product vector `|v_1 ⊗ ⋯ ⊗ v_q⟩` for a coloring `C : S → ι`: block `c` consists of the sites
`B_c = C⁻¹(c)`, its space `H_c` has the basis `{i // C i = c} → Fin d`, and the amplitude at a global basis
string `x` is `∏_c v_c(x|_{B_c})`. For an empty block the basis is a single point, so `H_c = ℂ` (the empty
tensor product convention of p.9). -/
def blockProd {S ι : Type} [Fintype ι] {d : ℕ} (C : S → ι)
    (v : ∀ c : ι, ({i // C i = c} → Fin d) → ℂ) : (S → Fin d) → ℂ :=
  fun x => ∏ c, v c (fun i => x i.1)

/-- **Block-product fidelity** `F_C`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (22), p.9: "For a coloring C : [n] → [q], let
B_c := C^{−1}(c) and H_{B_c} := ⊗_{i∈B_c} H_i for each c ∈ [q]. … If B_c = ∅, we use the empty tensor product
convention H_c = C. Define F_C(ρ) := max_{|v_c⟩∈H_c, ∥|v_c⟩∥_2=1, c∈[q]} ⟨v_1 ⊗ · · · ⊗ v_q|ρ|v_1 ⊗ · · · ⊗ v_q⟩."

**Formalization Note** The colour set is any finite type `ι` (the paper's `[q]` is `Fin q`); colorings with more
than `q` colours are used in the proof of Lemma 3.3 (ii), p.12–13. The maximum is `sSup` over unit families of
the real part of the quadratic form; the set is nonempty and bounded for `d ≥ 1`, and the supremum is attained. -/
noncomputable def fC {S ι : Type} [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι] {d : ℕ}
    (C : S → ι) (ρ : Matrix (S → Fin d) (S → Fin d) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ v : ∀ c : ι, ({i // C i = c} → Fin d) → ℂ, (∀ c, IsUnitVec (v c)) ∧
    r = (star (blockProd C v) ⬝ᵥ (ρ *ᵥ blockProd C v)).re}

/-- **`q`-block fidelity** `F_q`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), eq. (23), p.9: "We then minimize over all such colorings,
with at most q colors: F_q(ρ) := min_{C:[n]→[q]} F_C(ρ)."

**Formalization Note** A finite infimum over all `C : S → Fin q` (empty blocks allowed); for `q ≥ 1` it is the
printed minimum. Every statement using it has `q ≥ 1`. -/
noncomputable def fq {S : Type} [Fintype S] [DecidableEq S] {d : ℕ} (q : ℕ)
    (ρ : Matrix (S → Fin d) (S → Fin d) ℂ) : ℝ :=
  ⨅ C : S → Fin q, fC C ρ

end TolProdTest


