-- Prove2me | Definitions.Def_LatticePrepro_Tables_TableSoundness
-- name    : LatticePrepro_Tables_TableSoundness
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:21:59.710215+00:00
-- url     : https://prove2.me/theorems/1afa5563-93f5-4875-a3ea-d540f86aab7e
-- title:
--   Hankel length of the explicit tables, $\ell=p(B^m-1)+1$ (Construction A.4, Definition A.5)
-- statement:
--   For natural numbers $p,m,B$, `hLen p m B` is
--   $$\ell=p\,(B^m-1)+1,$$
--   the Hankel length $p(r-1)+1$ for the moment parameter $r=B^m$. In Construction A.4, $p$ is the characteristic, $m$ the number of axes and $B$ the base. Then $\ell$ is the size of the $\ell\times\ell$ polynomial matrix $H(X)=\bigl(P^y_{\mathrm{digits}(h)+\mathrm{digits}(h')}(X)\bigr)_{0\le h,h'<\ell}$ of an evaluation table $y$ (Definition A.5), and of the Hankel matrix $(\hat\mu_{h+h'}(y))_{0\le h,h'<\ell}$ of its moments.
--
--   Since $\ell-1=p(B^m-1)$, Claim A.2 with $J=p$ places $\mathrm{digits}(h)+\mathrm{digits}(h')$ in the index set $\{0,\dots,2p(B-1)\}^m$, and $2\ell-2=2p(B^m-1)$ is the largest moment order constrained by the tables.
--
--   **Formalization Note**: `hLen p m B` coincides with `hankelLen p (B ^ m)` from the Hankel reconstruction module. The polynomial matrix itself, and the matrix $(\lambda^{\mathrm{digits}(h)})$ used to analyse it, are defined in the source module but are not part of this bundle. The paper writes $\nu,\mathsf d,\mathsf a$ for $\ell,B,m$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Construction A.4, step 2 (\label{step:moment-parameters}) and Definition A.5 (\label{def:table-matrix}); Lean: LatticePrepro/Tables/TableSoundness.lean, LatticePrepro.ExplicitTables.hLen

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Construction

/-!
# Soundness of the explicit tables: the polynomial matrix (Definition A.5, Lemma A.6)

For a table `y` satisfying the constraints, the *polynomial matrix* `Hmat y` has entries
`P^y_{digits(h) + digits(h')} ∈ 𝕊[X]` (`0 ≤ h, h' < ℓ`, `ℓ = p (B^m - 1) + 1`). We show:

* its entries have degree `≤ Δ` (low-degree constraints);
* `Hmat y (s) = E · diag(y(·, s)) · Eᵀ`, so `∑_s rank Hmat y (s) ≤ wt(y)`;
* `Hmat y (γ)` is the Hankel matrix `(M̂_{h+h'}(y))` (index-consistency constraints);
* hence, by `card_mul_rank_eval_le`, the Hankel matrix has rank `ρ` with `(q - Δ) ρ ≤ wt(y)`,
  and its first `ρ + 1` columns are linearly dependent.
-/

namespace LatticePrepro

open Polynomial Matrix

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

/-- The Hankel length `ℓ = p (B^m - 1) + 1` (this is `hankelLen p (B^m)`). -/
def hLen (p m B : ℕ) : ℕ := p * (B ^ m - 1) + 1

variable {FS m B}

end ExplicitTables

end LatticePrepro


