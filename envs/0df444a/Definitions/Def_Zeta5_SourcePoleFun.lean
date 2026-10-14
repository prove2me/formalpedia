-- Prove2me | Definitions.Def_Zeta5_SourcePoleFun
-- name    : Zeta5_SourcePoleFun
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T19:19:56.477567+00:00
-- url     : https://prove2.me/theorems/0404bbd0-f1fd-4ab0-b580-fe780e04e3a6
-- title:
--   The tau_X toolkit: Bernoulli functional, binomial basis, poles and residues
-- statement:
--   This module reproduces the definitions used to *state* the $\tau_X$-bounds of the small-prime chain of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0: the Bernoulli functional `Lb Q = ∑ aₙ Bₙ`, the binomial basis `bin k = C(k!)⁻¹ · k!·C(x,k)` and `dcoef j = (-1)^{j-1}/j` (from `Apery/Arith/BinomBasis.lean`); the functional `tau P = Lb(P⁽³⁾)/24` and the binomial-representation predicate `BinRep p k r Q` (`Apery/Arith/TauBound.lean`); the residues `res K P j` of $P/D_K$ and the nodes/weights `node`, `weight` of the Hankel matrix $G_K$ (`Apery/Degree.lean`); and `piPl`, `polyPart`, `resP`, `dd`, `tauX` (`Apery/Arith/PoleFun.lean`), where $\tau_X(A, Pl) = \tau(A /_m \prod_{r \in Pl}(x-r)) + \sum_r \mathrm{resP}(A,Pl,r)(H^{(5)}_{d(r)} - X)$.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/PoleFun.lean + Apery/Arith/BinomBasis.lean + Apery/Arith/TauBound.lean + Apery/Degree.lean

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValToolkit

/-!
# The `τ_X` toolkit: Bernoulli functional, binomial basis, poles and residues

The definitions of `Apery/Arith/BinomBasis.lean`, `Apery/Arith/TauBound.lean`,
`Apery/Degree.lean` and `Apery/Arith/PoleFun.lean` that are needed to *state* the
`τ_X`-bounds of the small-prime chain:

* `Lb Q = ∑ a_n B_n` (the Bernoulli functional `L = Lb`);
* `bin k = C (k!)⁻¹ · k!·C(x,k)` (the binomial basis), `dcoef j = (-1)^{j-1}/j`;
* `tau P = Lb (P⁽³⁾)/24` and the binomial-representation predicate `BinRep p k r Q`;
* the residues `res K P j` of `P/D_K` and the nodes/weights `node`, `weight` of `G_K`;
* `piPl Pl = ∏_{r ∈ Pl} (x - r)`, the polynomial part `polyPart A Pl = A /ₘ piPl Pl`,
  the residues `resP A Pl r = A(r)/∏_{s ≠ r}(r - s)`, the harmonic index `dd` and
  `tauX A Pl = τ(polyPart A Pl) + ∑_r resP A Pl r · (H^{(5)}_{d(r)} - X)`.

Nothing is proved here; reproduced verbatim from mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

open Finset Polynomial

namespace Apery

/-! ### `Apery/Arith/BinomBasis.lean` -/

noncomputable def Lb (Q : ℚ[X]) : ℚ := Q.sum fun n a => a * _root_.bernoulli n

/-- `k! · C(x, k)`. -/
noncomputable def bin (k : ℕ) : ℚ[X] := C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k

noncomputable def dcoef (j : ℕ) : ℚ := (-1) ^ (j - 1) / (j : ℚ)

/-! ### `Apery/Arith/TauBound.lean` -/

noncomputable def tau (P : ℚ[X]) : ℚ := Lb (derivative^[3] P) / 24

/-- `Q` is a combination of `bin 0, …, bin k` with coefficients of valuation `≥ r`. -/
def BinRep (p : ℕ) (k : ℕ) (r : ℚ) (Q : ℚ[X]) : Prop :=
  ∃ e : ℕ → ℚ, Q = ∑ m ∈ range (k + 1), C (e m) * bin m ∧ ∀ m ≤ k, VG p (e m) r

/-! ### `Apery/Degree.lean` -/

/-- The residue `P(x_j)/D_K'(x_j)` at the root `x_j = -j²`. -/
noncomputable def res (K : ℕ) (P : ℚ[X]) (j : ℕ) : ℚ :=
  P.eval (-(j : ℚ) ^ 2) / (derivative (D K)).eval (-(j : ℚ) ^ 2)

noncomputable def node (n : ℕ) (k : Fin (37 * n)) : ℚ := -((3 * n + 1 + (k : ℕ) : ℕ) : ℚ) ^ 2

/-- The weights `w_k = D_N(x_k)^6 (N + 1 + k)^4 / D_K'(x_k)`. -/
noncomputable def weight (n : ℕ) (k : Fin (37 * n)) : ℚ :=
  (D (3 * n)).eval (node n k) ^ 6 * ((3 * n + 1 + (k : ℕ) : ℕ) : ℚ) ^ 4 /
    (derivative (D (40 * n))).eval (node n k)

/-! ### `Apery/Arith/PoleFun.lean` -/

/-- `∏_{r ∈ Pl} (x - r)`. -/
noncomputable def piPl (Pl : Finset ℤ) : ℚ[X] := ∏ r ∈ Pl, (X - C (r : ℚ))

/-- The polynomial part. -/
noncomputable def polyPart (A : ℚ[X]) (Pl : Finset ℤ) : ℚ[X] := A /ₘ piPl Pl

/-- The residue at `r`. -/
noncomputable def resP (A : ℚ[X]) (Pl : Finset ℤ) (r : ℤ) : ℚ :=
  A.eval (r : ℚ) / ∏ s ∈ Pl.erase r, ((r : ℚ) - s)

/-- The harmonic index `d(r)`. -/
def dd (r : ℤ) : ℕ := if 0 ≤ r then r.toNat else (-r - 1).toNat

/-- The functional `τ_X`. -/
noncomputable def tauX (A : ℚ[X]) (Pl : Finset ℤ) : ℚ[X] :=
  C (tau (polyPart A Pl)) + ∑ r ∈ Pl, C (resP A Pl r) * (C (H5 (dd r)) - X)

end Apery


