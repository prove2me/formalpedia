-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_Supplement_IdealState
-- name    : QuantumSepPoly_Frobenius_Supplement_IdealState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:49:19.181234+00:00
-- url     : https://prove2.me/theorems/4937fdcb-98f7-4fe1-9f76-d41b45fe6a40
-- title:
--   Ideal assignment mixture and smoothing
-- statement:
--   For an assignment $z$, put $v_z(i,a)=N^{-1/2}\mathbf1[a=z_i]$. The ideal state is the finite expectation
--   $$\psi=\mathbb E_{z\sim D}(v_zv_z^*)^{\otimes2k},$$
--   with the first $k$ and last $k$ registers forming its two parties. For an empirical matrix $\omega$, smoothing is
--   $$\widehat\omega=(1-\varepsilon/4)\omega+(\varepsilon/4)\frac{\mathrm{Id}}{(N|\Omega|)^{2k}}.$$
--   The mixture uses actual finite probability weights; no Bochner-integral default, correctness guarantee, or free ideal output is part of the definition.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Section 6, p. 29–31 (PDF p. 29–31); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Registers
import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Parameters

noncomputable section
open scoped BigOperators ENNReal

namespace QuantumSepPoly.Frobenius.Supplement
/-- v_z in one register, and its 2k-copy pure density across two blocks. -/
def assignmentVector {N A : ℕ} (z : Fin N → Fin A) : Register N A → ℂ :=
  fun i => if i.2 = z i.1 then 1/(Real.sqrt N : ℂ) else 0

def idealState {N A : ℕ} (k : ℕ) (D : PMF (Fin N → Fin A)) : TwoBlockOp N A k :=
  ∑ z, (D z).toReal • pure (fun x : Block N A k × Block N A k =>
    (∏ l, assignmentVector z (x.1 l)) * (∏ l, assignmentVector z (x.2 l)))

/-- Smoothing is applied to the empirically constructed matrix, not the ideal one. -/
def smooth {N A k : ℕ} (ε : ℚ) (ω : TwoBlockOp N A k) : TwoBlockOp N A k :=
  (1-(ε : ℝ)/4) • ω + ((ε : ℝ)/(4*((N*A : ℕ) : ℝ)^(2*k))) • 1
end QuantumSepPoly.Frobenius.Supplement


