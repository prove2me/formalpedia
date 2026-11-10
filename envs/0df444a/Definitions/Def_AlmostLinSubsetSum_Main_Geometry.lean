-- Prove2me | Definitions.Def_AlmostLinSubsetSum_Main_Geometry
-- name    : AlmostLinSubsetSum_Main_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:28:54.340212+00:00
-- url     : https://prove2.me/theorems/7b888607-f30c-4f00-b1e9-ac3bc88f122d
-- title:
--   Convex bodies, the body $K$, Macbeath regions $M^\lambda_K(p)$, boundary centers, fibers and $\psi^\pm$, the extended space $\mathbb R^{d+1}$
-- statement:
--   Objects of §4.4–§6.3.
--
--   - A **convex body** is a compact convex set $K\subset\mathbb R^d$ with nonempty interior.
--   - $M_p:=(K-p)\cap(p-K)=\{z : p+z\in K,\ p-z\in K\}$ and the **Macbeath region** $M^\lambda_K(p):=p+\lambda\cdot M_p$ (p. 21).
--   - For a zonotope $Z$, a box $Q$ with half-widths $q$, a window center $o\in\mathbb Z^d$, a constant $\eta$ and an integer scale $\tau$: $K:=(Z+10\eta\tau\cdot Q)\cap(o+3\tau\cdot Q)$ (p. 20).
--   - A **boundary center** (Definition 4.4, (11), p. 19) is a point $p\in Z\cap(o+2\tau\cdot Q)$ with $p+10\eta\tau\cdot Q\not\subseteq Z$. The paper's centers are moreover rational; this definition does not require it.
--   - For $J\subseteq\mathbb R^r$ and an integer matrix $F$, the fiber $J\cap F^{-1}(y)=\{u\in J: Fu=y\}$, and $\psi^-(y)$, $\psi^+(y)$ the minimum and maximum of $\psi\cdot u$ over it (p. 29). They are used only for $y\in FJ$, where the fiber is nonempty and compact (elsewhere Lean returns $0$).
--   - $\mathbb R^{d+1}$: `extend y z` is the point $(y,z)$, `proj` drops the last coordinate, and `extMap F ψ` is $u\mapsto(Fu,\psi\cdot u)$; `extendInt` is the integer point $(y,z)\in\mathbb Z^{d+1}$.
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, Definition 4.4 p. 19; §5.1 pp. 20–21; §6.3 p. 29

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

/-!
# Convex bodies, Macbeath regions, boundary centers, and the extended zonotope

Chen, Mao, Zhang (2026), STOC 2027 submission, SHA-256 0cd42ca0…1e0: Definition 4.4 and (11),
p. 19; the body `K` and the Macbeath regions, pp. 20–21; the extended space of §6.3, p. 29.

**Formalization Note.**
* `IsConvexBody K`: compact, convex, with nonempty interior in `ℝ^d` (`Fin d → ℝ`).
* `macbeathM K p = (K − p) ∩ (p − K)`, written as `{z | p + z ∈ K ∧ p − z ∈ K}`.
* `psiMinus`/`psiPlus` are the minimum and maximum of `ψ · u` over the fiber `J ∩ F⁻¹(y)`,
  as real `sInf`/`sSup`; they are only used at points `y ∈ FJ`, where the fiber is nonempty
  and compact (for `y ∉ FJ` the value is Lean's junk `0`).
* `ℝ^{d+1}` is `Fin (d + 1) → ℝ`; `extend y z` is the point `(y, z)` (last coordinate `z`),
  and `proj x` drops the last coordinate.
-/

/-- A convex body in `ℝ^d`: a compact convex set with nonempty interior. -/
def IsConvexBody {d : ℕ} (K : Set (Fin d → ℝ)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- `M_p := (K − p) ∩ (p − K)`, the set of `z` with `p + z ∈ K` and `p − z ∈ K`. -/
def macbeathM {d : ℕ} (K : Set (Fin d → ℝ)) (p : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {z | p + z ∈ K ∧ p - z ∈ K}

/-- The Macbeath region `M^λ_K(p) := p + λ · M_p`. -/
def macbeathRegion {d : ℕ} (K : Set (Fin d → ℝ)) (c : ℝ) (p : Fin d → ℝ) : Set (Fin d → ℝ) :=
  translate p (dilate c (macbeathM K p))

/-- The body of §5.1 (p. 20): `K := (Z + 10ητ · Q) ∩ (o + 3τ · Q)` for the zonotope `Z`, the
box `Q` with half-widths `q`, the window center `o`, the constant `η` and the scale `τ`. -/
def shellBody {d : ℕ} (Z : Set (Fin d → ℝ)) (q : Fin d → ℝ) (o : Fin d → ℤ) (η : ℝ) (τ : ℕ) :
    Set (Fin d → ℝ) :=
  minkSum Z (dilate (10 * η * τ) (box q)) ∩ translate (toReal o) (dilate (3 * τ) (box q))

/-- A boundary center (Definition 4.4, (11), p. 19): a point `p ∈ Z ∩ (o + 2τ · Q)` with
`p + 10ητ · Q ⊄ Z`. (The paper's centers are moreover rational; that is not required here.) -/
def IsBoundaryCenter {d : ℕ} (Z : Set (Fin d → ℝ)) (q : Fin d → ℝ) (o : Fin d → ℤ) (η : ℝ)
    (τ : ℕ) (p : Fin d → ℝ) : Prop :=
  p ∈ Z ∧ p ∈ translate (toReal o) (dilate (2 * τ) (box q)) ∧
    ¬ translate p (dilate (10 * η * τ) (box q)) ⊆ Z

/-- The fiber `K ∩ F⁻¹(y) = {u ∈ K : F u = y}` of a set `K ⊆ ℝ^r` over `y ∈ ℝ^d`. -/
def fiber {d r : ℕ} (K : Set (Fin r → ℝ)) (F : Matrix (Fin d) (Fin r) ℤ) (y : Fin d → ℝ) :
    Set (Fin r → ℝ) :=
  {u | u ∈ K ∧ realMap F u = y}

/-- `ψ⁻(y)`: the minimum of `ψ · u` over `u ∈ J ∩ F⁻¹(y)`. -/
noncomputable def psiMinus {d r : ℕ} (J : Set (Fin r → ℝ)) (F : Matrix (Fin d) (Fin r) ℤ)
    (ψ : Fin r → ℤ) (y : Fin d → ℝ) : ℝ :=
  sInf ((fun u => toReal ψ ⬝ᵥ u) '' fiber J F y)

/-- `ψ⁺(y)`: the maximum of `ψ · u` over `u ∈ J ∩ F⁻¹(y)`. -/
noncomputable def psiPlus {d r : ℕ} (J : Set (Fin r → ℝ)) (F : Matrix (Fin d) (Fin r) ℤ)
    (ψ : Fin r → ℤ) (y : Fin d → ℝ) : ℝ :=
  sSup ((fun u => toReal ψ ⬝ᵥ u) '' fiber J F y)

/-- The point `(y, z) ∈ ℝ^{d+1}`. -/
def extend {d : ℕ} (y : Fin d → ℝ) (z : ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) y z

/-- The projection of `x ∈ ℝ^{d+1}` to its first `d` coordinates. -/
def proj {d : ℕ} (x : Fin (d + 1) → ℝ) : Fin d → ℝ :=
  Fin.init (α := fun _ => ℝ) x

/-- The integer point `(y, z) ∈ ℤ^{d+1}`. -/
def extendInt {d : ℕ} (y : Fin d → ℤ) (z : ℤ) : Fin (d + 1) → ℤ :=
  Fin.snoc (α := fun _ => ℤ) y z

/-- The map `(F, ψ) : u ↦ (F u, ψ · u)` from `ℝ^r` to `ℝ^{d+1}`. -/
def extMap {d r : ℕ} (F : Matrix (Fin d) (Fin r) ℤ) (ψ : Fin r → ℤ) (u : Fin r → ℝ) :
    Fin (d + 1) → ℝ :=
  extend (realMap F u) (toReal ψ ⬝ᵥ u)

end AlmostLinSubsetSum.Main


