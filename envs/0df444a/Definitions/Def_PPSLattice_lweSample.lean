-- Prove2me | Definitions.Def_PPSLattice_lweSample
-- name    : PPSLattice_lweSample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:35:25.689865+00:00
-- url     : https://prove2.me/theorems/8f253628-5a70-4413-aa54-fbdf361be0b7
-- title:
--   The LWE sample distributions $(\mathbf A,\mathbf s^\top\mathbf A+\mathbf e^\top)$ and $(\mathbf A,\mathbf c^\top)$
-- statement:
--   For a dimension $n$, a modulus $q$, a number of samples $m$ and a width $\chi$: $\mathbf A\leftarrow\mathbb Z_q^{n\times m}$ uniform and
--
--   1. (real) $\mathbf b^\top=\mathbf s^\top\mathbf A+\mathbf e^\top$ with $\mathbf s\leftarrow\mathbb Z_q^n$ uniform and $\mathbf e\leftarrow D^m_{\mathbb Z,\chi}$ reduced modulo $q$;
--   2. (random) $\mathbf b^\top=\mathbf c^\top\leftarrow\mathbb Z_q^m$ uniform.
--
--   The output is the pair $(\mathbf A,\mathbf b)$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17

import Mathlib
import Definitions.Def_PPSLattice_uniformMat
import Definitions.Def_PPSLattice_dGaussZq
set_option autoImplicit false

namespace PPSLattice

/-- The two **LWE sample distributions** with dimension `n`, modulus `q`, `m` samples and Gaussian
width `χ`: the pair `(A, b)` with `A ← Z_q^{n×m}` uniform and
1. `b = s^⊤A + e^⊤` with `s ← Z_q^n` uniform and `e ← D^m_{Z,χ}` reduced modulo `q` (`real = true`),
2. `b = c ← Z_q^m` uniform (`real = false`).
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17 ("{(A, s^⊤A + e^⊤)} ≈c {(A, c^⊤)} where m ∈ N, A ← Z_q^{n×m}, s ← Z_q^n,
e ← D^m_{Z,χ}, c ← Z_q^m").

**Formalization Note.** Row vectors are functions `Fin m → ZMod q`; `(s^⊤A)_j = Σ_i s_i A_{ij}`. -/
noncomputable def lweSample (q n m : ℕ) (χ : ℝ) (real : Bool) :
    PMF (Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ZMod q)) :=
  (uniformMat q n m).bind fun A =>
    (if real then
        (iidVec (uniformZq q) n).bind fun s =>
          (iidVec (dGaussZq q χ) m).map fun e => fun j => (∑ i, s i * A i j) + e j
      else iidVec (uniformZq q) m).map fun b => (A, b)

end PPSLattice


