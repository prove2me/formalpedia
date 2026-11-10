-- Prove2me | Definitions.Def_EllipticRootFinding_Online_Curves
-- name    : EllipticRootFinding_Online_Curves
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:02:42.160802+00:00
-- url     : https://prove2.me/theorems/ff624ec8-96d4-45b3-946a-205957a28dd5
-- title:
--   Short Weierstrass curves, split divisors and elliptic preprocessing data
-- statement:
--   For $a, b \in F$ let $E_{a,b}$ be the short Weierstrass curve $Y^2 = X^3 + aX + b$ and $\mathrm{Pt}(a,b)$ its rational points: the point at infinity $\infty$ (written $0$) and the nonsingular affine solutions, with the chord-and-tangent group law of Mathlib. For a nonsquare $\beta$, the **quadratic twist** of $E_{a,b}$ by $\beta$ is represented by $Y^2 = X^3 + a\beta^{-2}X + b\beta^{-3}$. A point $P$ lies in the $n$-torsion subgroup $E[n]$ when $[nP] = \infty$. A point is encoded as $[\,]$ if it is $\infty$ and as $[x, y]$ otherwise.
--
--   A **split divisor** is a finite set $S$ of points. It is **simple** when $\infty \notin S$ and the $x$-coordinates of its points are pairwise distinct; its **$(u, v)$-coordinates** are then $u = \prod_{P \in S}(X - x(P))$ and the polynomial $v$ with $\deg v < \deg u$ and $v(x(P)) = y(P)$ for $P \in S$. A **representation** of a split divisor $S$ is a flag for $\infty$ together with a list of $(u, v)$-coordinates of simple divisors with pairwise disjoint supports, whose supports together with $\infty$ (if flagged) form $S$; it is input as $[\text{flag}, [[u_1, v_1], \dots]]$.
--
--   An **elliptic preprocessing datum** $D = (\beta, E, \tilde E, N, \tilde N, \mathrm{fac}(N), \mathrm{fac}(\tilde N), G_1, G_2, \tilde G_1, \tilde G_2)$ consists of $\beta, a, b \in F$, integers $N, \tilde N$, two lists of pairs (prime, exponent), points $G_1, G_2$ of $E = E_{a,b}$ and $\tilde G_1, \tilde G_2$ of the twist $\tilde E$. It is **valid** when $\beta$ is a nonsquare, $4a^3 + 27b^2 \neq 0$, $N = |E(F)|$, $\tilde N = |\tilde E(F)|$, the lists are the prime factorizations of $N$ and $\tilde N$, and
--   $$E(F) = \langle G_1\rangle \oplus \langle G_2\rangle, \qquad \tilde E(F) = \langle \tilde G_1\rangle \oplus \langle \tilde G_2\rangle$$
--   as internal direct sums ($G_2 = \infty$ is allowed). $\Xi(D)$ is the largest prime dividing $N \tilde N$. The online input on $F$ with $q$ elements is $[q, f, \beta, a, b, N, \tilde N, \mathrm{fac}(N), \mathrm{fac}(\tilde N), G_1, G_2, \tilde G_1, \tilde G_2]$.
--
--   **Formalization Note.** Validity is a hypothesis of the goal, never something the program checks; $\Xi(D)$ is computed from $N$ and $\tilde N$, not from the factorization lists.
-- source:
--   Spaenlehauer, Deterministic Root-Finding over Finite Fields with Elliptic Curves, arXiv:2610.32508 (version held, sha256 c72ee273…), p. 2, Definition 1.2; p. 12, §3 (short Weierstrass models, quadratic twist); p. 13 (torsion, Ξ); p. 17, Definition 4.3

import Mathlib
import Definitions.Def_EllipticRootFinding_Online_Machine

namespace EllipticRootFinding.Online

/-!
# Short Weierstrass curves, split divisors and elliptic preprocessing data

Spaenlehauer, arXiv:2610.32508 (version held): p. 12 (§3, short Weierstrass models, the quadratic
twist `Y² = X³ + aβ⁻²X + bβ⁻³`), p. 13 (torsion, `ℓ`-Sylow subgroup, `Ξ`), p. 17 (Definition 4.3,
split and simple divisors and their `(u, v)`-coordinates), p. 2 (Definition 1.2, elliptic
preprocessing datum, and `Ξ(D)`).

Points are Mathlib's `WeierstrassCurve.Affine.Point` (the point at infinity `0` and the nonsingular
affine points) with its chord-and-tangent group law.
-/

open Polynomial

/-- The short Weierstrass curve `Y² = X³ + aX + b`. -/
def shortCurve {F : Type} [Field F] (a b : F) : WeierstrassCurve F where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := a
  a₆ := b

/-- The rational points `E(F)` of `Y² = X³ + aX + b`: `∞` (written `0`) and the affine points. -/
abbrev Pt {F : Type} [Field F] (a b : F) : Type :=
  WeierstrassCurve.Affine.Point (shortCurve a b).toAffine

/-- Coefficient `aβ⁻²` of the quadratic twist `Ẽ` of `Y² = X³ + aX + b` by `β` (p. 12). -/
def twistA {F : Type} [Field F] (a β : F) : F := a * (β ^ 2)⁻¹

/-- Coefficient `bβ⁻³` of the quadratic twist `Ẽ` of `Y² = X³ + aX + b` by `β` (p. 12). -/
def twistB {F : Type} [Field F] (b β : F) : F := b * (β ^ 3)⁻¹

/-- The `x`-coordinate of an affine point (`0` at `∞`, never used there). -/
def ptX {F : Type} [Field F] {a b : F} : Pt a b → F
  | .zero => 0
  | .some x _ _ => x

/-- The `y`-coordinate of an affine point (`0` at `∞`, never used there). -/
def ptY {F : Type} [Field F] {a b : F} : Pt a b → F
  | .zero => 0
  | .some _ y _ => y

/-- Encoding of a point: `∞ ↦ []`, `(x, y) ↦ [x, y]`. -/
def pointVal {F : Type} [Field F] {a b : F} : Pt a b → Val F
  | .zero => Val.nil
  | .some x y _ => Val.ofList [Val.fld x, Val.fld y]

/-- `P` lies in the `n`-torsion subgroup `E(F)[n]`: `[nP] = ∞`. -/
def IsTors {F : Type} [Field F] [DecidableEq F] {a b : F} (n : ℕ) (P : Pt a b) : Prop :=
  n • P = 0

/-- `(u, v)` are the `(u, v)`-coordinates of the simple divisor with support `S`
(Definition 4.3): `S` avoids `∞`, its points have pairwise distinct `x`-coordinates,
`u = ∏_{P ∈ S} (X − x(P))`, `deg v < deg u` and `v(x(P)) = y(P)` for `P ∈ S`. -/
def SimpleUV {F : Type} [Field F] {a b : F} (u v : F[X]) (S : Finset (Pt a b)) : Prop :=
  (∀ P ∈ S, P ≠ .zero) ∧ Set.InjOn ptX (S : Set (Pt a b)) ∧
    u = ∏ P ∈ S, (X - C (ptX P)) ∧ v.degree < u.degree ∧ ∀ P ∈ S, v.eval (ptX P) = ptY P

/-- A representation of the split divisor with support `S` (p. 17): a flag `inf` for `∞` and a
list of `(u, v)`-coordinates of simple divisors with pairwise disjoint supports, whose supports,
together with `∞` if `inf`, make up `S`. -/
def RepresentsSplit {F : Type} [Field F] {a b : F} (inf : Bool) (L : List (F[X] × F[X]))
    (S : Finset (Pt a b)) : Prop :=
  open Classical in
  ∃ Ss : List (Finset (Pt a b)),
    List.Forall₂ (fun uv T => SimpleUV uv.1 uv.2 T) L Ss ∧ Ss.Pairwise Disjoint ∧
      S = Ss.foldr (· ∪ ·) (if inf then {.zero} else ∅)

/-- Input encoding of a split-divisor representation: `[flag, [[u₁, v₁], …, [u_k, v_k]]]`. -/
noncomputable def splitVal {F : Type} [Field F] (inf : Bool) (L : List (F[X] × F[X])) : Val F :=
  Val.ofList [Val.int (if inf then 1 else 0),
    Val.ofList (L.map fun uv => Val.ofList [polyVal uv.1, polyVal uv.2])]

/-- Output reading: `w` is (the layout of) some representation of the split divisor with
support `S`, polynomials read by `IsPolyVal`. -/
def IsSplitVal {F : Type} [Field F] {a b : F} (w : Val F) (S : Finset (Pt a b)) : Prop :=
  ∃ (inf : Bool) (L : List (F[X] × F[X])) (ws : List (Val F × Val F)),
    w = Val.ofList [Val.int (if inf then 1 else 0),
      Val.ofList (ws.map fun pv => Val.ofList [pv.1, pv.2])] ∧
    List.Forall₂ (fun pv uv => IsPolyVal pv.1 uv.1 ∧ IsPolyVal pv.2 uv.2) ws L ∧
    RepresentsSplit inf L S

/-- `fac` is the prime factorization of `n`: pairs `(r, k)` with `r` prime, `k ≥ 1`, distinct
primes, and `∏ r^k = n`. -/
def IsFactorization (n : ℕ) (fac : List (ℕ × ℕ)) : Prop :=
  (∀ rk ∈ fac, rk.1.Prime ∧ 1 ≤ rk.2) ∧ (fac.map Prod.fst).Nodup ∧
    (fac.map fun rk => rk.1 ^ rk.2).prod = n

/-- Encoding of a factorization: `[[r₁, k₁], …]`. -/
def facVal {F : Type} (fac : List (ℕ × ℕ)) : Val F :=
  Val.ofList (fac.map fun rk => Val.ofList [Val.int (rk.1 : ℤ), Val.int (rk.2 : ℤ)])

/-- `G₁, G₂` form a basis of the group: `E(F) = ⟨G₁⟩ ⊕ ⟨G₂⟩` (internal direct sum:
the cyclic subgroups generate and meet trivially). `G₂ = ∞` is allowed. -/
def IsBasis {F : Type} [Field F] [DecidableEq F] {a b : F} (G₁ G₂ : Pt a b) : Prop :=
  AddSubgroup.zmultiples G₁ ⊔ AddSubgroup.zmultiples G₂ = ⊤ ∧
    Disjoint (AddSubgroup.zmultiples G₁) (AddSubgroup.zmultiples G₂)

/-- The components of an elliptic preprocessing datum (Definition 1.2):
`D = (β, E, Ẽ, N, Ñ, fac(N), fac(Ñ), G₁, G₂, G̃₁, G̃₂)`, with `E : Y² = X³ + aX + b` and
`Ẽ : Y² = X³ + aβ⁻²X + bβ⁻³`. -/
structure Datum (F : Type) [Field F] where
  β : F
  a : F
  b : F
  N : ℕ
  Nt : ℕ
  facN : List (ℕ × ℕ)
  facNt : List (ℕ × ℕ)
  G₁ : Pt a b
  G₂ : Pt a b
  Gt₁ : Pt (twistA a β) (twistB b β)
  Gt₂ : Pt (twistA a β) (twistB b β)

/-- Validity of a datum (Definition 1.2): `β` is a nonsquare (hence nonzero), `E` is an elliptic
curve (`4a³ + 27b² ≠ 0`), `N = |E(F)|`, `Ñ = |Ẽ(F)|`, `fac(N)`, `fac(Ñ)` are their prime
factorizations, and `(G₁, G₂)`, `(G̃₁, G̃₂)` are bases of `E(F)` and `Ẽ(F)`. -/
def Datum.Valid {F : Type} [Field F] [DecidableEq F] (D : Datum F) : Prop :=
  ¬ IsSquare D.β ∧ 4 * D.a ^ 3 + 27 * D.b ^ 2 ≠ 0 ∧
    D.N = Nat.card (Pt D.a D.b) ∧ D.Nt = Nat.card (Pt (twistA D.a D.β) (twistB D.b D.β)) ∧
    IsFactorization D.N D.facN ∧ IsFactorization D.Nt D.facNt ∧
    IsBasis D.G₁ D.G₂ ∧ IsBasis D.Gt₁ D.Gt₂

/-- `Ξ(D)`: the largest prime dividing `N · Ñ` (`0` if there is none). -/
def Datum.Xi {F : Type} [Field F] (D : Datum F) : ℕ :=
  (D.N * D.Nt).primeFactors.sup id

/-- Input layout of the online phase on `F` with `q` elements:
`[q, f, β, a, b, N, Ñ, fac(N), fac(Ñ), G₁, G₂, G̃₁, G̃₂]`. -/
noncomputable def onlineInput {F : Type} [Field F] (q : ℕ) (f : F[X]) (D : Datum F) : Val F :=
  Val.ofList [Val.int (q : ℤ), polyVal f, Val.fld D.β, Val.fld D.a, Val.fld D.b,
    Val.int (D.N : ℤ), Val.int (D.Nt : ℤ), facVal D.facN, facVal D.facNt,
    pointVal D.G₁, pointVal D.G₂, pointVal D.Gt₁, pointVal D.Gt₂]

end EllipticRootFinding.Online


