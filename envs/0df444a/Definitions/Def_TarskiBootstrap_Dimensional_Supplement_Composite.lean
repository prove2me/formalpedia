-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_Supplement_Composite
-- name    : TarskiBootstrap_Dimensional_Supplement_Composite
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:04:24.297206+00:00
-- url     : https://prove2.me/theorems/69d34ec0-4fd3-4ce8-85ff-5c139f8fc096
-- title:
--   The composite problem $\mathrm{OS}_m\circ(\mathrm{Tarski}^H|_{\mathcal F'},\dots)$
-- statement:
--   Fix $A$, $\mathcal F$ and $m$. The composite problem has index set $\{1,\dots,m\}\times[n]^k$. Its domain $\mathcal D$ (equation (2.13)) consists of the strings $x$ on this index set such that, for every $r$, the block $z\mapsto x(r,z)$ is an input of $\mathrm{Tarski}^H|_{\mathcal F'}$, and the vector of inner answers $\bigl(\mathrm{Tarski}^H(x(r,\cdot))\bigr)_{r}$ is an $\mathrm{OS}_m$ instance. The composite function (2.12) applies $\mathrm{OS}_m$ to that vector. For signs $s=(s_1,\dots,s_m)$ and maps $f=(f_1,\dots,f_m)$, the oracle of the input $(s,f)$ is
--
--   $$
--   h(r,z)=H_{s_r}(f_r)(z)=\bigl(f_r(z),\ \sigma^{f_r}_{s_r}(z)\bigr).
--   $$
--
--   This is the abstract problem that the staircase construction embeds into a grid.
--
--   **Formalization Note** Positions $1,\dots,m$ are encoded by `Fin m`.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Definition 2.9, equations (2.11)–(2.13), PDF/printed p. 8; §4.2–4.3, pp. 19, 21, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_HiddenSign
import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_OrderedSearch

namespace TarskiBootstrap.Dimensional.Supplement

/-- The oracle `h(r, z) = H_{s_r}(f_r)(z) = (f_r(z), σ_{s_r}^{f_r}(z))` of the composite
input `(s, f)`, on the index set `{1, …, m} × [n]^k` of (2.11) (positions encoded by
`Fin m`), PDF/printed pp. 19, 21. -/
noncomputable def compositeOracle {n k : ℕ+} {m : ℕ+} (A : Set (Grid n k))
    (s : Fin (m : ℕ) → SignType) (f : Fin (m : ℕ) → Grid n k → Grid n k) :
    Fin (m : ℕ) × Grid n k → Grid n k × SignType :=
  fun p => hiddenSignOracle A (s p.1) (f p.1) p.2

/-- The domain (2.13), p. 8, of `OS_m ∘ (Tarski^H(n,k)|F′, …, Tarski^H(n,k)|F′)`:
strings on `{1, …, m} × [n]^k` whose `r`-th block is an input of `Tarski^H|F′` for
every `r`, and whose vector of inner answers is an `OS_m` instance. -/
noncomputable def compositeDomain {n k : ℕ+} (A : Set (Grid n k))
    (F : Set (Grid n k → Grid n k)) (m : ℕ+) :
    Set (Fin (m : ℕ) × Grid n k → Grid n k × SignType) :=
  {x | (∀ r, (fun z => x (r, z)) ∈ hiddenSignFamily A F) ∧
    ∃ i, (fun r => tarskiHAnswer (fun z => x (r, z))) = osInstance m i}

/-- The composite function (2.12), p. 8: `OS_m` applied to the vector of inner
`Tarski^H` answers. -/
noncomputable def compositeAnswer {n k : ℕ+} (m : ℕ+)
    (x : Fin (m : ℕ) × Grid n k → Grid n k × SignType) : Fin (m : ℕ) :=
  osOutput m (fun r => tarskiHAnswer (fun z => x (r, z)))

end TarskiBootstrap.Dimensional.Supplement


