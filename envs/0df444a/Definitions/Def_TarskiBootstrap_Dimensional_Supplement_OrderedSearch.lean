-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_Supplement_OrderedSearch
-- name    : TarskiBootstrap_Dimensional_Supplement_OrderedSearch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:02:33.490619+00:00
-- url     : https://prove2.me/theorems/bbafa6b1-a629-4457-a1dc-b79f8ef88817
-- title:
--   Ordered search $\mathrm{OS}_m$ and $\mathrm{SA}(\mathrm{OS}_m)$
-- statement:
--   For a positive integer $m$ and a hidden position $i\in\{1,\dots,m\}$, the ordered search instance is the string $f_i:\{1,\dots,m\}\to\{-1,0,1\}$ given by
--
--   $$
--   f_i(j)=\begin{cases}1,& j<i,\\ 0,& j=i,\\ -1,& j>i.\end{cases}
--   $$
--
--   The problem $\mathrm{OS}_m$ asks for the hidden position $i$ given oracle access to $f_i$. Its spectral adversary value $\mathrm{SA}(\mathrm{OS}_m)$ is the value (2.8) of the output map on the $m$ instance strings.
--
--   These objects enter the statement of the logarithmic bootstrapping theorem, whose amplification factor is $\mathrm{SA}(\mathrm{OS}_m)$.
--
--   **Formalization Note** Positions $1,\dots,m$ are encoded by `Fin m` $=\{0,\dots,m-1\}$ with the same order. The output map returns the hidden position of an instance string (instances are pairwise distinct) and an arbitrary fixed position on other strings, which never enter.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Definition 2.2, PDF/printed p. 6; equation (2.8), p. 7, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_SpectralAdversary

namespace TarskiBootstrap.Dimensional.Supplement

/-- Definition 2.2, PDF/printed p. 6: the ordered search instance with hidden position
`i`, `f_i(j) = 1` for `j < i`, `0` for `j = i`, `-1` for `j > i`. Positions
`1, …, m` are encoded as `Fin m = {0, …, m-1}` with the same order. -/
def osInstance (m : ℕ+) (i : Fin (m : ℕ)) : Fin (m : ℕ) → SignType :=
  fun j => if j < i then 1 else if j = i then 0 else -1

/-- The output of `OS_m`: the hidden position of an ordered search instance. Off the
instances (never used) it returns the first position. -/
noncomputable def osOutput (m : ℕ+) (t : Fin (m : ℕ) → SignType) : Fin (m : ℕ) := by
  classical
  exact if h : ∃ i, osInstance m i = t then h.choose else ⟨0, m.pos⟩

/-- `SA(OS_m)`, the spectral adversary value (2.8) of ordered search on its `m`
instances. -/
noncomputable def osSA (m : ℕ+) : ℝ :=
  spectralAdversary (Set.range (osInstance m)) (osOutput m)

end TarskiBootstrap.Dimensional.Supplement


