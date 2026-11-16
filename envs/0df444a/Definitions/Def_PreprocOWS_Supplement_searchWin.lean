-- Prove2me | Definitions.Def_PreprocOWS_Supplement_searchWin
-- name    : PreprocOWS_Supplement_searchWin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:07:25.555188+00:00
-- url     : https://prove2.me/theorems/1e426b2a-abf5-410c-bf0b-596b7d4424bc
-- title:
--   Oracle state search game: winning probability $\mathbb E_k\|\Pi_k O_f V|\psi_{R,k}\rangle\|^2$
-- statement:
--   This definition fixes the one-query normal form (Definition 3.10) and the search game (Definition 9.1).
--
--   1. An **isometry** is a matrix $V:\mathbb C^N\to\mathbb C^M$ with $V^\dagger V = I_N$; it is the computation before the oracle query.
--   2. For a Boolean function $f:[M]\to\{\pm1\}$ the **arbitrary phase oracle** is the diagonal matrix $O_f|i\rangle = f(i)|i\rangle$ on the $M$-dimensional workspace.
--   3. For an oracle $R:[K]\times[N]\to\{\pm1\}$, a projective measurement $\{\Pi_k\}_{k\in[K]}$ on $\mathbb C^M$ and a phase function $f$, the winning probability of the **oracle state search game** is
--   $$
--   \mathbb E_{k}\,\big\|\Pi_k\,O_f\,V\,|\psi_{R,k}\rangle\big\|^2,\qquad |\psi_{R,k}\rangle = \frac1{\sqrt N}\sum_{x\in[N]}R(k,x)|x\rangle,
--   $$
--   with $k$ uniform on $[K]$. The paper's $\mathrm{Win}(\mathcal A\mid R)$ is the maximum of this quantity over $f$.
--
--   $V$ and $\{\Pi_k\}$ do not depend on $R$; only $f$ may. The post-query unitary is absorbed into $\{\Pi_k\}$, as on the page.
--
--   **Formalization Note** Bits encode signs: $f$ is Boolean-valued and $\mathrm{true}\mapsto -1$, as for the oracle $R$ of the base mission.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Definition 3.10, p.14 (PDF p.17); Definition 9.1, p.33 (PDF p.36)

import Mathlib
import Definitions.Def_PreprocOWS_vnormSq
import Definitions.Def_PreprocOWS_chal
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- `V : ℂ^N → ℂ^M` is an **isometry**: `V† V = I_N` (arXiv:2610.02101, Definition 3.10, p.14,
PDF p.17: "an isometry `V : C^N → C^M`", equivalently `∑_i |v_i⟩⟨v_i| = I_N`). -/
def IsIsometry {M N : ℕ} (V : Matrix (Fin M) (Fin N) ℂ) : Prop :=
  Vᴴ * V = 1

/-- The **arbitrary phase oracle** `O_f |i⟩ = f(i) |i⟩` on the `M`-dimensional workspace, for a
Boolean function `f : [M] → {±1}` (arXiv:2610.02101, Definition 3.10, p.14; Definition 9.1, p.33).

**Formalization Note.** `f` is Bool-valued with sign `sgn` (`true ↦ −1`), as for the oracle `R`. -/
def phaseF {M : ℕ} (f : Fin M → Bool) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.diagonal fun i => sgn (f i)

/-- The winning probability `E_k ‖Π_k · O_f · V |ψ_{R,k}⟩‖²` of the **oracle state search game** for a
fixed phase function `f`, Dong–Lombardi, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…),
Definition 9.1, p.33 (PDF p.36). The page's `Win(𝒜 | R)` is the maximum of this over `f`.

**Formalization Note.** `V` (an isometry `ℂ^N → ℂ^M`) and the projective measurement `{Π_k}` are
fixed independently of `R`; only `f` may depend on `R` (the theorems quantify over maps `R ↦ f`).
The post-query unitary is absorbed into `{Π_k}` as on the page. `k` is uniform on `[K]`. -/
noncomputable def searchWin {K N M : ℕ} (V : Matrix (Fin M) (Fin N) ℂ)
    (P : Fin K → Matrix (Fin M) (Fin M) ℂ) (f : Fin M → Bool) (R : Oracle K N) : ℝ :=
  (K : ℝ)⁻¹ * ∑ k, vnormSq (P k *ᵥ (phaseF f *ᵥ (V *ᵥ chal R k)))

end PreprocOWS.Supplement


