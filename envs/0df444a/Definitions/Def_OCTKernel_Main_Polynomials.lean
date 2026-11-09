-- Prove2me | Definitions.Def_OCTKernel_Main_Polynomials
-- name    : OCTKernel_Main_Polynomials
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:20.886705+00:00
-- url     : https://prove2.me/theorems/5fceb648-3add-4683-b78b-f1450d4dab91
-- title:
--   Polynomial Wronskians and maximal root multiplicities
-- statement:
--   For $s$ polynomials $f_0,\ldots,f_{s-1}$ over a field, their **Wronskian** is
--
--   $$\operatorname{Wr}(f)=\det\bigl(f_i^{(j)}\bigr)_{0\le i,j<s}.$$
--
--   For a polynomial subspace $W$ and a field element $\alpha$, define
--
--   $$\nu_W(\alpha)=\sup\{\operatorname{mult}(f,\alpha):f\in W,\ f\ne0\}.$$
--
--   In Lemma 3.3 the space is nonzero and its degrees are bounded, so this supremum is a finite maximum. Outside that regime the natural-number supremum is a total operation: it returns zero on the empty or unbounded set; the lemmas never rely on those defaults. The zero polynomial is explicitly excluded.
-- source:
--   Tomohiro Koana, Soh Kumabe, A Deterministic Polynomial Kernel for Odd Cycle Transversal, STOC 2027 submission #810 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/810.pdf, SHA-256 043624e22f147583799f7dcc844cebbd4644ecdc53a42543f708cda5c38c6b72, §3.3, pp.7–8

import Mathlib

set_option autoImplicit false

namespace OCTKernel.Main

/-- The s-fold polynomial Wronskian, §3.3 p.7, with indices starting at zero. -/
noncomputable def wronskian {K : Type} [Field K] {s : ℕ}
    (f : Fin s → Polynomial K) : Polynomial K :=
  Matrix.det (fun i j : Fin s => (Polynomial.derivative^[j.val]) (f i))

/-- Maximum multiplicity over nonzero members, §3.3 p.8.
For the bounded-degree nonzero spaces in Lemma 3.3 this set is nonempty and bounded. -/
noncomputable def nu {K : Type} [Field K] (W : Submodule K (Polynomial K)) (α : K) : ℕ :=
  sSup {h | ∃ f ∈ W, f ≠ 0 ∧ h = f.rootMultiplicity α}

end OCTKernel.Main


