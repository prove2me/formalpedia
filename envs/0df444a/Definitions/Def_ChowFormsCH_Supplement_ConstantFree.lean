-- Prove2me | Definitions.Def_ChowFormsCH_Supplement_ConstantFree
-- name    : ChowFormsCH_Supplement_ConstantFree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:18:56.882443+00:00
-- url     : https://prove2.me/theorems/c7c45096-662f-4fe3-9238-4f6f4e87cbed
-- title:
--   Constant-free rational arithmetic circuits and the polynomials they compute
-- statement:
--   An arithmetic circuit over $\mathbb{Q}$ (Definition 2.6) is a directed acyclic graph whose sources are input gates labelled by variables $x_i$ or constant gates labelled by rational numbers, and whose internal gates are labelled $+$, $\times$ or $\div$; no division by zero may occur in $\mathbb{Q}(x)$. The circuit is **constant-free** if its only constants are $0$, $+1$ and $-1$.
--
--   This definition provides:
--
--   1. the predicate `ConstantFree C` on circuits of the published model `APSCounting893.Main.ArithmeticCircuit` read over $\mathbb{Q}$;
--   2. the polynomials $f_1, \dots, f_m \in \mathbb{Q}[x]$ computed by the output gates, and their images in $K[x]$ for any field $K$ of characteristic zero (such as $\overline{\mathbb{Q}}$ or $\mathbb{C}$);
--   3. the row-by-row listing $a_{0,0}, \dots, a_{0,s-1}, a_{1,0}, \dots$ of a grid of values, matching the order of the Chow-form variables $u_{i,j}$.
--
--   These are the input conventions of Theorems 1.1–1.6.
--
--   **Formalization Note** In the published circuit model a constant gate carries the coordinate list of a scalar; over $\mathbb{Q}$ the lists `[]`, `[0]`, `[1]`, `[-1]` denote $0, 0, 1, -1$. The model's extra subtraction gate adds no power: $x - y = x + (-1)\cdot y$.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Definition 2.6, p.11 (PDF p.13); §3.1, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_APSCounting893_Main_CircuitInputs

set_option autoImplicit false

namespace ChowFormsCH.Supplement

open APSCounting893.Main

/-- A rational arithmetic circuit is **constant-free**: every constant gate is labelled by `0`,
`+1` or `−1` (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH via
Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, Definition 2.6, p.11: "If the only
constants labeling the input gates of the circuit are 0, +1, and −1, we say that the circuit is
constant-free").

**Formalization Note** Circuits are the published `APSCounting893.Main.ArithmeticCircuit`, read
over `ℚ` (`CoefficientPresentation.rational`), whose constant gate carries the coordinate list of
a scalar; over `ℚ` a valid coordinate list has length at most one, and the lists `[]`, `[0]`,
`[1]`, `[-1]` are the scalars `0, 0, 1, −1`. Division gates are allowed, as in Definition 2.6;
the extra `sub` gate of that circuit model computes `x − y = x + (−1)·y` and adds no power. -/
def ConstantFree {n : ℕ} (C : ArithmeticCircuit n) : Prop :=
  ∀ g ∈ C.gates, ∀ cs : List ℚ, g = ArithmeticGate.constant cs →
    cs = [] ∨ cs = [0] ∨ cs = [1] ∨ cs = [-1]

/-- The coefficient field of `CoefficientPresentation.rational` is `ℚ`. -/
noncomputable def ratFieldEquiv : CoefficientPresentation.rational.Field ≃+* ℚ :=
  RingEquiv.refl ℚ

/-- The polynomials `f₁, …, f_m ∈ ℚ[x]` computed by a rational circuit `C` (the outputs of `C`,
in order), with coefficients moved into a field `K` of characteristic zero (for instance the
algebraic closure of `ℚ`, or `ℂ`). -/
noncomputable def ratPolys (K : Type*) [Field K] [CharZero K] {n : ℕ} (C : ArithmeticCircuit n)
    (j : Fin C.outputs.length) : MvPolynomial (Fin n) K :=
  MvPolynomial.map ((algebraMap ℚ K).comp ratFieldEquiv.toRingHom)
    (circuitPolynomials CoefficientPresentation.rational C j)

/-- The rational polynomials computed by `C`, as elements of `ℚ[x]`. -/
noncomputable def ratPolysQ {n : ℕ} (C : ArithmeticCircuit n) (j : Fin C.outputs.length) :
    MvPolynomial (Fin n) ℚ :=
  MvPolynomial.map ratFieldEquiv.toRingHom (circuitPolynomials CoefficientPresentation.rational C j)

/-- The entries of a grid `a : Fin r × Fin s → α`, listed row by row:
`a(0,0), …, a(0,s−1), a(1,0), …` (the order `u_{0,0}, …, u_{0,n}, u_{1,0}, …` of the variables of a
Chow form, §3.1, p.21). -/
def gridList {α : Type*} {r s : ℕ} (a : Fin r × Fin s → α) : List α :=
  (List.finRange r).flatMap (fun i => (List.finRange s).map (fun j => a (i, j)))

end ChowFormsCH.Supplement


