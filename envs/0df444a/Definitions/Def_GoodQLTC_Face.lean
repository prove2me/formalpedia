-- Prove2me | Definitions.Def_GoodQLTC_Face
-- name    : GoodQLTC_Face
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:43:26.843227+00:00
-- url     : https://prove2.me/theorems/a8770ba2-3738-486e-8bd5-e2d1f29bc4c7
-- title:
--   The set $X(j)$ of $j$-faces and $Z_j=|X(j)|$
-- statement:
--   For a cubical complex $X$ and $j\in\mathbb N$, $X(j)=\{f\in X:\dim f=j\}$ is the set of $j$-dimensional faces, and $Z_j=|X(j)|$.
--
--   **Formalization Note** A subtype of $X$ with classical finiteness and decidable-equality instances.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §4.1, p.15 (PDF p.18); Z_j, §7, p.23

import Mathlib
import Definitions.Def_GoodQLTC_dir

namespace GoodQLTC

/-- The set `X(j) := {f ∈ X : dim f = j}` of `j`-dimensional faces, Gay–Jeronimo,
arXiv:2609.20780 (held version), §4.1, p.15, as a type.

**Formalization Note.** A subtype of `X`; its `Fintype` and `DecidableEq` instances are classical. -/
def Face {X : Type} {t : ℕ} (φ : X → Fin t → Option Bool) (j : ℕ) : Type :=
  {f : X // fdim φ f = j}

noncomputable instance {X : Type} [Fintype X] {t : ℕ} (φ : X → Fin t → Option Bool) (j : ℕ) :
    Fintype (Face φ j) := by
  classical
  unfold Face
  infer_instance

noncomputable instance {X : Type} {t : ℕ} (φ : X → Fin t → Option Bool) (j : ℕ) :
    DecidableEq (Face φ j) :=
  Classical.decEq _

/-- `Z_j := |X(j)|`, the number of `j`-faces (arXiv:2609.20780, §7, p.23). -/
noncomputable def numFaces {X : Type} [Fintype X] {t : ℕ} (φ : X → Fin t → Option Bool) (j : ℕ) :
    ℕ :=
  Fintype.card (Face φ j)

end GoodQLTC


