-- Prove2me | Definitions.Def_ImplicitParityWL_Exposure
-- name    : ImplicitParityWL_Exposure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:58.872846+00:00
-- url     : https://prove2.me/theorems/85626564-72aa-44e1-80f6-393e76066642
-- title:
--   Exposed coordinates, variables and equations $I_v(\mathcal A)$, $I_e(\mathcal A)$, $\mathrm{Var}(\mathcal A)$, $\mathrm{Eqs}(\mathcal A)$
-- statement:
--   For a set $\mathcal A$ of colors, the coordinate sets $I_v(\mathcal A)\subseteq\mathfrak c_v$ and $I_e(\mathcal A)\subseteq\mathfrak c_e$ are the smallest sets such that
--
--   1. if $\mathcal A$ contains the coordinate color $\mathrm{crd}_{v,c}$, then $c\in I_v(\mathcal A)$;
--   2. if $\mathcal A$ contains a color of internal track ($1\le h\le k+1$), update, sum or junction vertices of the schema $e$ at $c\in\mathfrak c_e$, then $c\in I_e(\mathcal A)$, and $\sigma(c)\in I_u(\mathcal A)$, $\tau(c)\in I_v(\mathcal A)$, and $\pi(c)\in I_w(\mathcal A)$ for a ternary schema.
--
--   Mask color classes add no coordinates. A variable $X_{v,a}$ is **exposed** if $\mathrm{supp}(a)\subseteq I_v(\mathcal A)$, and the equation of $e$ at an allowed address $a$ is exposed if $\mathrm{supp}(a)\subseteq I_e(\mathcal A)$. $\mathrm{Var}(\mathcal A)$ and $\mathrm{Eqs}(\mathcal A)$ are the exposed variables and equations.
--
--   These sets are what Duplicator's strategy must keep consistent with unit propagation.
--
--   **Formalization Note** The two rules are not recursive, so the smallest sets are written as explicit unions. A name that is not a color class of the compiled graph adds nothing. An assignment on $\mathrm{Var}(\mathcal A)$ is a total function of which only those values are read.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Definition 5.8, pp.29–30

import Mathlib
import Definitions.Def_ImplicitParityWL_CompiledGraph

namespace ImplicitParityWL

namespace ImplicitSystem

variable {k ℓ : ℕ} {W E : Type*} (I : ImplicitSystem k ℓ W E)

/-- The set of colors `A` contains a color of internal track (`1 ≤ h ≤ k + 1`), update, sum or junction
vertices of the schema `e` at the coordinate `c ∈ 𝔠_e` (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for
the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, Definition 5.8,
p.30). This is the membership condition of `I_e(A)`.

**Formalization Note** A name that is not a color class of the compiled graph (a `sum` color of a binary
schema, a `trk` color at an index outside `[1, k + 1]`) adds nothing. -/
def InternalAt (A : Finset (CColor k ℓ W E)) (e : E) (c : Coord k ℓ) : Prop :=
  c ∈ (I.schema e).dom ∧
    ((∃ h, 1 ≤ h ∧ h ≤ k + 1 ∧ CColor.trk e h c ∈ A) ∨
     (∃ h, 1 ≤ h ∧ h ≤ k + 2 ∧ CColor.upd e h c ∈ A) ∨
     ((I.schema e).third.isSome ∧ (CColor.sum e c ∈ A ∨ CColor.junc e c ∈ A)))

/-- The coordinate set `I_e(A) ⊆ 𝔠_e` (Definition 5.8, p.30). -/
def Ie (A : Finset (CColor k ℓ W E)) (e : E) : Set (Coord k ℓ) := {c | I.InternalAt A e c}

/-- The coordinate set `I_v(A) ⊆ 𝔠_v` (Definition 5.8, pp.29–30).

**Formalization Note** The page defines the `I_v(A)` and `I_e(A)` as the smallest sets closed under its two
rules. The rules are not recursive, so the smallest sets are these explicit unions: `c ∈ 𝔠_v` with the color
`crd_{v,c}` in `A`, and the images `σ(c₀)`, `τ(c₀)`, `π(c₀)` of coordinates `c₀` in `I_e(A)` for the schemas
`e` with argument location `v`. Mask colors add no coordinates. -/
def Iv (A : Finset (CColor k ℓ W E)) (v : W) : Set (Coord k ℓ) :=
  {c | (c ∈ I.dom v ∧ CColor.crd v c ∈ A) ∨
    ∃ (e : E) (c₀ : Coord k ℓ), I.InternalAt A e c₀ ∧
      (((I.schema e).u = v ∧ c = (I.schema e).σ c₀) ∨
       ((I.schema e).v = v ∧ c = (I.schema e).τ c₀) ∨
       ∃ π, (I.schema e).third = some (v, π) ∧ c = π c₀)}

/-- `Var(A)`, the variables exposed for `A` (Definition 5.8, p.30): `X_{v,a}` with `supp(a) ⊆ I_v(A)`. -/
def Var (A : Finset (CColor k ℓ W E)) : Set (W × Address k ℓ) :=
  {X | (X.2.supp : Set (Coord k ℓ)) ⊆ I.Iv A X.1}

/-- `Eqs(A)`, the equations exposed for `A` (Definition 5.8, p.30): the equation of a schema `e` at an address
`a` with `supp(a) ⊆ I_e(A)`. -/
def Eqs (A : Finset (CColor k ℓ W E)) : Set (Finset (W × Address k ℓ)) :=
  {h | ∃ (e : E) (a : Address k ℓ),
    (a.supp : Set (Coord k ℓ)) ⊆ I.Ie A e ∧ h = (I.schema e).equation a}

/-- The assignment `α` satisfies all equations exposed for `A`: each sums to zero (§4.1, p.16). All variables
of an exposed equation are exposed (Definition 5.8, p.30).

**Formalization Note** An assignment on `Var(A)` is a total function of which only the values on `Var(A)` are
read. -/
def SatisfiesExposed (A : Finset (CColor k ℓ W E)) (α : W × Address k ℓ → ZMod 2) : Prop :=
  ∀ h ∈ I.Eqs A, ∑ X ∈ h, α X = 0

/-- The assignment `α` on `Var(A)` agrees with `K_r` (§4.1, p.16): `α(X) = b` for all `(X, b) ∈ K_r` with
`X ∈ Var(A)`. -/
def AgreesWith (A : Finset (CColor k ℓ W E)) (α : W × Address k ℓ → ZMod 2) (r : ℕ) : Prop :=
  ∀ X b, (X, b) ∈ I.toParity.K r → X ∈ I.Var A → α X = b

end ImplicitSystem

end ImplicitParityWL


