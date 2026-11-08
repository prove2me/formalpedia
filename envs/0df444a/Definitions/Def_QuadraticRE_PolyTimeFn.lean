-- Prove2me | Definitions.Def_QuadraticRE_PolyTimeFn
-- name    : QuadraticRE_PolyTimeFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:09:18.73172+00:00
-- url     : https://prove2.me/theorems/f328f577-4330-4dff-b924-4962775aa0ed
-- title:
--   Polynomial time, bit encodings and the public parameters $(\mathrm{rep},1^\lambda)$
-- statement:
--   A map between bit strings is **polynomial-time computable** if one fixed Turing machine computes it within a fixed polynomial of the input length. Inputs are written as bit strings: natural numbers in unary ($n$ ones followed by a zero), bit vectors bit by bit, a representation as $N$, $b$ and, for each program, $k$, $s$, $t$ and its $k\times k$ label table; a description as $N,\rho,\ell$ and its monomial lists; a straight-line program as its gates and output positions. The **public parameters** of Definition 3.7 are a representation $\mathrm{rep}$ and $1^\lambda$ with $\lambda\ge1$.
--
--   These encodings make "polynomial in $\sigma+\lambda$" a statement about machines.
--
--   **Formalization Note** The machine model is Mathlib's `Turing.TM2ComputableInPolyTime` over the alphabet `Bool`. Because every number, in particular $\lambda$, is in unary, the encoded parameters have length at least $\sigma+\lambda$ and at most a fixed cubic polynomial in $\sigma+\lambda$; this and the injectivity and prefix property of the encodings are proved in the verification file.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Definition 3.7, pp.15–16; §3.2, p.14

import Mathlib
import Definitions.Def_QuadraticRE_Rep
import Definitions.Def_QuadraticRE_Desc
import Definitions.Def_QuadraticRE_SLP

namespace QuadraticRE

/-- Polynomial time, the reading of Definition 3.7 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), pp.15–16: one fixed machine
(Mathlib's `Turing.TM2ComputableInPolyTime`) that from the bit string `ea a` outputs the bit string
`f a`, within a fixed polynomial in the length of `ea a`. -/
def PolyTimeFn {α : Type} (ea : α → List Bool) (f : α → List Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime ea (id : List Bool → List Bool) f)

/-- A natural number in unary, self-delimiting: `n` ones, then a zero. This is `1^n`. -/
def encNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- A list of natural numbers, each in unary. -/
def encTokens (l : List ℕ) : List Bool := l.flatMap encNat

/-- The bits of a vector, in order. -/
def bits {n : ℕ} (v : Fin n → F2) : List Bool := List.ofFn fun i => decide (v i = 1)

/-- A decoder's answer: `⊥` is `[false]`, `y` is `true` followed by the bits of `y`. -/
def encOpt {n : ℕ} : Option (Fin n → F2) → List Bool
  | none => [false]
  | some y => true :: bits y

/-- An entry of a label table: no edge, `1`, `x_i`, `1 + x_i`. -/
def cellToken {N : ℕ} : Option (Lit N) → ℕ
  | none => 0
  | some .one => 1
  | some (.pos i) => 2 + 2 * i.val
  | some (.neg i) => 3 + 2 * i.val

/-- A program: `k`, `s`, `t` and the `k × k` label table in row order. -/
def bpTokens {N : ℕ} (P : BP N) : List ℕ :=
  [P.k, P.s.val, P.t.val] ++
    (List.finRange P.k).flatMap fun u => (List.finRange P.k).map fun v => cellToken (P.label u v)

/-- A representation: `N`, `b`, then the programs. -/
def repTokens (rep : Rep) : List ℕ :=
  [rep.N, rep.b] ++ rep.bps.flatMap bpTokens

/-- The public parameters `(rep, 1^λ)` of Definition 3.7, p.15, `λ ≥ 1`. -/
structure Param where
  rep : Rep
  lam : ℕ
  hlam : 1 ≤ lam

/-- The bit encoding of `(rep, 1^λ)`. All numbers are in unary, in particular `λ`, so the length is
polynomially related to `σ + λ` (both bounds are proved in the verification file). -/
def encParam (p : Param) : List Bool := encTokens (repTokens p.rep ++ [p.lam])

/-- The bit encoding of one branching program with its input length. -/
def encBP (p : Σ N, BP N) : List Bool := encTokens (p.1 :: bpTokens p.2)

/-- A variable: `x_i` is `2i`, `r_i` is `2i + 1`. -/
def varToken {N ρ : ℕ} : Fin N ⊕ Fin ρ → ℕ
  | .inl i => 2 * i.val
  | .inr i => 2 * i.val + 1

/-- A description: `N, ρ, ℓ`, then per coordinate the number of monomials and, per monomial, the number
of variables and the variables. -/
def descTokens {N ρ ℓ : ℕ} (D : Desc N ρ ℓ) : List ℕ :=
  [N, ρ, ℓ] ++ (List.finRange ℓ).flatMap fun i =>
    (D.coords i).length :: (D.coords i).flatMap fun m => m.length :: m.map varToken

/-- The bit encoding of a description, whose length is the "expanded polynomial description" size. -/
def encDesc {N ρ ℓ : ℕ} (D : Desc N ρ ℓ) : List Bool := encTokens (descTokens D)

/-- A gate, with `tok` naming the inputs. -/
def gateTokens {ι : Type} (tok : ι → ℕ) : Gate ι → List ℕ
  | .input i => [0, tok i]
  | .one => [1]
  | .add g g' => [2, g, g']
  | .mul g g' => [3, g, g']

/-- The bit encoding of a straight-line program: number of gates, the gates, the output positions. -/
def encSLP {ι : Type} {m : ℕ} (tok : ι → ℕ) (P : SLP ι (Fin m)) : List Bool :=
  encTokens (P.gates.length :: P.gates.flatMap (gateTokens tok) ++ (List.finRange m).map P.outs)

end QuadraticRE


