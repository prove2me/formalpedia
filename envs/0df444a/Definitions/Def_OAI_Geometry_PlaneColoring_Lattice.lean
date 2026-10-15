-- Prove2me | Definitions.Def_OAI_Geometry_PlaneColoring_Lattice
-- name    : OAI_Geometry_PlaneColoring_Lattice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T17:36:28.285852+00:00
-- url     : https://prove2.me/theorems/cc0b0e0e-53e4-44c6-8575-017f5a88622e
-- title:
--   The norm form $a^2+ab+b^2$ and the seven-coloring $a+3b \bmod 7$ of the triangular lattice
-- statement:
--   Index the points of the triangular lattice by integer pairs $(a,b)\in\mathbb{Z}^2$, the pair $(a,b)$ standing for the point $a\,e_1+b\,e_2$ with the unit vectors $e_1=(1,0)$ and $e_2=\bigl(\tfrac12,\tfrac{\sqrt3}{2}\bigr)$, which meet at an angle of $60^\circ$. The file defines integer arithmetic for this lattice.
--
--   1. **Norm form.** For $a,b\in\mathbb{Z}$,
--   $$N(a,b)=a^2+ab+b^2\in\mathbb{Z}.$$
--   Since $e_1\cdot e_2=\tfrac12$, this is the squared Euclidean length $\|a\,e_1+b\,e_2\|^2$ in the triangular lattice of unit spacing.
--   2. **Seven-coloring.** For $a,b\in\mathbb{Z}$,
--   $$\kappa(a,b)=a+3b \pmod 7\ \in\ \mathbb{Z}/7\mathbb{Z}.$$
--   3. **Seven-coloring with values in $\{0,1,\dots,6\}$.** The same map $\kappa$, with its residues read as elements of the seven-element set $\{0,1,\dots,6\}$, so that it can serve as the color assignment of a coloring with $7$ colors.
--
--   Two lattice points $(a,b)$ and $(c,d)$ receive the same color exactly when $7$ divides $(a-c)+3(b-d)$, that is, when their difference lies in the index-seven sublattice $\{(p,q)\in\mathbb{Z}^2:\ p+3q\equiv0 \pmod 7\}$. On that sublattice the identity $N(p,q)=(p+3q)(p-2q)+7q^2$ shows $7\mid N(p,q)$, so two distinct points of the same color are at squared lattice distance at least $7$. This is the arithmetic behind the classical seven-coloring of the plane built on the triangular lattice.
--
--   **Formalization Note** `normSq a b` is integer-valued; `color a b` takes values in `ZMod 7`, and `colorFin a b` is the same value viewed in `Fin 7` (for modulus $7$ the two types coincide definitionally).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/PlaneColoring/Lattice.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/PlaneColoring/Lattice.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PlaneColoring mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PlaneColoring

namespace OAI

/-! Integer arithmetic for the classical seven-color triangular lattice. -/

namespace Problem160
namespace SevenLattice

/-- Squared Euclidean norm in a triangular lattice of unit spacing. -/
def normSq (a b : ℤ) : ℤ := a ^ 2 + a * b + b ^ 2

/-- The index-seven coloring of triangular-lattice sites. -/
def color (a b : ℤ) : ZMod 7 := (a : ZMod 7) + 3 * (b : ZMod 7)

/-- The colors can be used directly as the `Fin 7` target of a coloring. -/
def colorFin (a b : ℤ) : Fin 7 := color a b

end SevenLattice
end Problem160

end OAI


