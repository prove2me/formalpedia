-- Prove2me | Definitions.Def_PrivLittlestone_rankOf
-- name    : PrivLittlestone_rankOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:33:44.35905+00:00
-- url     : https://prove2.me/theorems/4c7ea62f-5b0d-4802-a2d8-7fa3f7fb81c0
-- title:
--   Structural rank $\rho(h) = \max\{s : h \in F_s\}$
-- statement:
--   The **structural rank** of $h \in U$ is $\rho(h) = \max\{ s \in \{0, \dots, d\} : h \in F_s \}$.
--
--   **Formalization Note** The value $0$ off $U$ is never used.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Appendix A.2.1, p.17

import Mathlib
import Definitions.Def_PrivLittlestone_rankLayer

namespace PrivLittlestone

open Classical in
/-- The **structural rank** `ρ(h) = max{s : h ∈ F_s}` (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
Appendix A.2.1, p.17), the largest `s ∈ {0, …, d}` with `h ∈ F_s`.

**Formalization Note** `Nat.findGreatest`; the value `0` off `U` is never used. -/
noncomputable def rankOf {X : Type*} (H : Set (X → Bool)) (d : ℕ) (h : X → Bool) : ℕ :=
  Nat.findGreatest (fun s => h ∈ rankLayer H d s) d

end PrivLittlestone


