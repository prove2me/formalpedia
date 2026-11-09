-- Prove2me | Definitions.Def_ProxGapTight_shorten
-- name    : ProxGapTight_shorten
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:43.505253+00:00
-- url     : https://prove2.me/theorems/730240ef-8a0e-4e84-9954-c28bb94f5ed0
-- title:
--   Shortening $D[S]=D\cap R^S$
-- statement:
--   For $S\subseteq\iota$ let $R^S=\{v\in R^\iota:\ \mathrm{supp}(v)\subseteq S\}$ be the words supported on $S$. The **shortening** of a linear code $D\subseteq R^\iota$ to $S$ is
--   $$
--   D[S]=D\cap R^S.
--   $$
--
--   Lemma 3.4 controls the shortenings of the ambient code $U_m$ to small sets $S$; this is how low-weight codewords are pinned down.
--
--   **Formalization Note** Both $R^S$ (helper `supportedOn`) and $D[S]$ are submodules; $S$ is a finite set of coordinates.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §2, p.6, display

import Mathlib

namespace ProxGapTight

/-- The subspace `R^S := {v ∈ R^ι : supp(v) ⊆ S}` of words supported on `S ⊆ ι`, Kominers, Thaler,
Zheng, manuscript (Sept. 2026), §2, p.6, display. -/
def supportedOn (R : Type) {ι : Type} [Semiring R] (S : Finset ι) : Submodule R (ι → R) where
  carrier := {v | ∀ i, i ∉ S → v i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c v hv i hi
    simp [hv i hi]

/-- The **shortening** `D[S] := D ∩ R^S` of a linear code `D ⊆ R^ι` to `S ⊆ ι`, Kominers, Thaler,
Zheng, manuscript (Sept. 2026), §2, p.6, display.

**Formalization Note.** `S` is a `Finset` of the (finite) coordinate type; the intersection is the
submodule infimum. -/
def shorten {R ι : Type} [Semiring R] (D : Submodule R (ι → R)) (S : Finset ι) :
    Submodule R (ι → R) :=
  D ⊓ supportedOn R S

end ProxGapTight


