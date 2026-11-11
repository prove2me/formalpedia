-- Prove2me | Definitions.Def_QBennettGill_boxD0
-- name    : QBennettGill_boxD0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:09:14.319383+00:00
-- url     : https://prove2.me/theorems/164eeafe-19f5-436e-8589-6ddd211355fc
-- title:
--   The distributions $\mathcal D_0$ and $\mathcal D_1$ of Box 1
-- statement:
--   Let $H:\{0,1\}^n\to\{0,1\}^n$, $p\in\mathbb N$ and $r=(r_1,\dots,r_p)\in\{0,1\}^p$. Put $I_0=\{i:r_i=0\}$, $I_1=\{i:r_i=1\}$, $\mathrm{Image}=\{y:\exists z,\ H(z)=y\}$ and $\mathrm{PreImage}(y)=\{z:H(z)=y\}$.
--
--   - **$\mathcal D_0(n,H,p,r)$.** Independently for each $i$:
--     - if $r_i=0$, sample $y_i\xleftarrow{\$}\mathrm{Image}$ and then $v_i\xleftarrow{\$}\mathrm{PreImage}(y_i)$;
--     - if $r_i=1$, sample $y_i\xleftarrow{\$}\{0,1\}^n\setminus\mathrm{Image}$.
--   - **$\mathcal D_1(n,H,p,r)$.** Independently for each $i$, sample $v_i\xleftarrow{\$}\{0,1\}^n$ and set $y_i=H(v_i)$.
--
--   Both output $T=(\{r_i\}_{i\in[p]},\{y_i\}_{i\in[p]},\{v_i\}_{i\in I_0})$.
--
--   **Formalization Note** The output is encoded as $(r,(y_i)_i,(v_i)_i)$ with $v_i:=0^n$ for $i\in I_1$, which is not part of the output. Sampling from the empty set $\{0,1\}^n\setminus\mathrm{Image}$ (when $H$ is a permutation) returns $0^n$, one of the two conventions offered on p.17. Strings are `Fin n → ZMod 2` (`BBBV.RandomOracle.Str n`).
-- source:
--   Liang, Yamakawa, Yung, Structured Quantum Hardness from Unstructured Assumptions, STOC 2027 submission (held manuscript, sha256 6464b75a…), Box 1, p.25 (PDF p.28); §3 Notation, p.17 (PDF p.20)

import Definitions.Def_BBBV_RandomOracle_QueryModel

set_option autoImplicit false

namespace QBennettGill

open BBBV.RandomOracle

/-- `Image := {y ∈ {0,1}ⁿ | ∃z, H(z) = y}`. -/
def imageSet {n : ℕ} (H : Str n → Str n) : Finset (Str n) := Finset.univ.image H

/-- `PreImage(y) := {z ∈ {0,1}ⁿ | H(z) = y}`. -/
def preImageSet {n : ℕ} (H : Str n → Str n) (y : Str n) : Finset (Str n) :=
  Finset.univ.filter (fun z => H z = y)

/-- A **transcript** `T = ({r_i}_{i∈[p]}, {y_i}_{i∈[p]}, {v_i}_{i∈I₀})` of Box 1, with `v_i := 0ⁿ` in the slots
`i ∈ I₁` (which are not part of the output). -/
abbrev Transcript (n p : ℕ) : Type := (Fin p → Bool) × (Fin p → Str n) × (Fin p → Str n)

open Classical in
/-- The weight of one coordinate `(y_i, v_i)` under **`D₀`** (Box 1): if `r_i = 0`, `y_i ←$ Image` and
`v_i ←$ PreImage(y_i)`; if `r_i = 1`, `y_i ←$ {0,1}ⁿ \ Image` (and `v_i` is not output). Sampling from the
empty set `{0,1}ⁿ \ Image` (`H` onto) returns `0ⁿ`. -/
noncomputable def d0Coord {n : ℕ} (H : Str n → Str n) (ri : Bool) (y v : Str n) : ℝ :=
  if ri = false then
    (if H v = y then 1 / (((imageSet H).card : ℝ) * ((preImageSet H y).card : ℝ)) else 0)
  else if v = 0 then
    (if (Finset.univ \ imageSet H).Nonempty then
      (if y ∉ imageSet H then 1 / ((Finset.univ \ imageSet H).card : ℝ) else 0)
    else (if y = 0 then 1 else 0))
  else 0

open Classical in
/-- The weight of one coordinate under **`D₁`** (Box 1): `v_i ←$ {0,1}ⁿ`, `y_i := H(v_i)`, and `v_i` is output
only if `r_i = 0`. -/
noncomputable def d1Coord {n : ℕ} (H : Str n → Str n) (ri : Bool) (y v : Str n) : ℝ :=
  if ri = false then (if H v = y then 1 / (Fintype.card (Str n) : ℝ) else 0)
  else if v = 0 then ((preImageSet H y).card : ℝ) / (Fintype.card (Str n) : ℝ) else 0

open Classical in
/-- **Distribution `D₀(n, H, p, r)`** of Box 1, as a weight function on transcripts (coordinates
independent).

Liang, Yamakawa, Yung, *Structured Quantum Hardness from Unstructured Assumptions*, STOC 2027
submission (held manuscript, sha256 6464b75a…), Box 1, p.25 (PDF p.28).

**Formalization Note.** Strings `{0,1}ⁿ` are `Fin n → ZMod 2` (the published `BBBV.RandomOracle.Str`);
the empty-set convention of p.17 ("⊥ or 0ⁿ") is `0ⁿ`. -/
noncomputable def boxD0 {n p : ℕ} (H : Str n → Str n) (r : Fin p → Bool) (T : Transcript n p) : ℝ :=
  if T.1 = r then ∏ i, d0Coord H (r i) (T.2.1 i) (T.2.2 i) else 0

open Classical in
/-- **Distribution `D₁(n, H, p, r)`** of Box 1, as a weight function on transcripts.

Liang, Yamakawa, Yung, *Structured Quantum Hardness from Unstructured Assumptions*, STOC 2027
submission (held manuscript, sha256 6464b75a…), Box 1, p.25 (PDF p.28). -/
noncomputable def boxD1 {n p : ℕ} (H : Str n → Str n) (r : Fin p → Bool) (T : Transcript n p) : ℝ :=
  if T.1 = r then ∏ i, d1Coord H (r i) (T.2.1 i) (T.2.2 i) else 0

end QBennettGill


