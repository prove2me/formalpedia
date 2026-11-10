-- Prove2me | Definitions.Def_OptGaussTomo_beamSplitter
-- name    : OptGaussTomo_beamSplitter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:06:15.14567+00:00
-- url     : https://prove2.me/theorems/5c869521-e78f-4cdb-a469-9515e106929a
-- title:
--   The balanced beam splitter $S_{\mathrm{bs}}$ on two $m$-mode systems
-- statement:
--   On two $m$-mode systems, with quadratures ordered (system 1, system 2) and interleaved within each system, the balanced beam splitter is the symplectic matrix
--
--   $$
--   S_{\mathrm{bs}}=\frac1{\sqrt2}\begin{pmatrix}I&-I\\ I&I\end{pmatrix},
--   $$
--
--   where $I$ is the $2m\times2m$ identity.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma D.12 p.55 (pdf p.55)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Support50.P14 (OscillatorCovariance)

namespace OptGaussTomo

/-!
# The balanced beam splitter `S_bs` on two m-mode systems

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), Lemma D.12, p.55:
"the balanced beam splitter acting on two m-mode systems, i.e. … the symplectic matrix
`S_bs = (1/√2) [I −I; I I]`, where `I` is the `2m × 2m` identity matrix."

**Formalization Note.** The two systems are the modes `Fin m ⊕ Fin m` (`Sum.inl` = system 1,
`Sum.inr` = system 2), the quadratures `(Fin m ⊕ Fin m) × Fin 2` (interleaved within each
system). The block `(a, b)` of `S_bs` (rows in system `a`, columns in system `b`) is
`(1/√2) I` except the block (system 1, system 2), which is `−(1/√2) I`, as printed.
-/

/-- `S_bs = (1/√2)[I −I; I I]` on `(Fin m ⊕ Fin m) × Fin 2`. -/
noncomputable def beamSplitter (m : ℕ) : OscillatorCovariance (Fin m ⊕ Fin m) :=
  fun a b =>
    match a.1, b.1 with
    | Sum.inl i, Sum.inl j => if i = j ∧ a.2 = b.2 then 1 / Real.sqrt 2 else 0
    | Sum.inl i, Sum.inr j => if i = j ∧ a.2 = b.2 then -(1 / Real.sqrt 2) else 0
    | Sum.inr i, Sum.inl j => if i = j ∧ a.2 = b.2 then 1 / Real.sqrt 2 else 0
    | Sum.inr i, Sum.inr j => if i = j ∧ a.2 = b.2 then 1 / Real.sqrt 2 else 0

end OptGaussTomo


