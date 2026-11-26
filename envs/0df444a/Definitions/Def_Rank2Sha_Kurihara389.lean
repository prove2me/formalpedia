-- Prove2me | Definitions.Def_Rank2Sha_Kurihara389
-- name    : Rank2Sha_Kurihara389
-- status  : Definition
-- author  : @barindersbanwait
-- created : 2026-11-25T22:35:01.814733+00:00
-- url     : https://prove2.me/theorems/952bb2fc-9fb7-4dda-aebc-4f1cbc745f1d
-- title:
--   Kolyvagin primes, Kurihara numbers and the tame discriminant of 389a1
-- statement:
--   Let $E$ be the elliptic curve $y^2 + y = x^3 + x^2 - 2x$ over $\mathbb{Q}$ (LMFDB 389.a1), and $P_1 = (0,0)$, $P_2 = (-1,1)$, a basis of $E(\mathbb{Q})$. Let $p$ be a prime. For a prime $l \ne 389$ write $E(\mathbb{F}_l)$ for the group of points of the reduction of $E$ modulo $l$, $N_l = \#E(\mathbb{F}_l)$, and $\bar P$ for the reduction of a point $P$.
--
--   1. A **Kolyvagin prime** for $p$ is a prime $l \ne 389$ with $l \equiv 1 \pmod p$ such that $E(\mathbb{F}_l)[p]$ has exactly $p$ elements, that is, $E(\mathbb{F}_l)[p]$ is cyclic of order $p$.
--   2. $\eta_l$ is the least primitive root modulo $l$, and for $a$ prime to $l$, $\lambda_l(a) \in \mathbb{F}_p$ is the discrete logarithm of $a$ to the base $\eta_l$, reduced modulo $p$.
--   3. For distinct Kolyvagin primes $l_1, l_2$ for $p$, the **Kurihara number** is
--
--   $$
--   \delta_{l_1 l_2} = \sum_{a \in (\mathbb{Z}/l_1l_2\mathbb{Z})^\times} \Big[ \frac{a}{l_1 l_2} \Big]^+ \lambda_{l_1}(a)\, \lambda_{l_2}(a) \ \in \mathbb{F}_p ,
--   $$
--
--   where $[r]^+$ is the plus modular symbol of $E$ normalised by $\Omega^+ = \int_{E(\mathbb{R})}|\omega|$ (definition `Rank2Sha_PlusSymbol389`).
--   4. For a Kolyvagin prime $l$ and $P, Q \in E(\mathbb{Q})$ put $h_l(P, Q) = \lambda_l\big(\tau_l((N_l/p)\bar P, \bar Q)\big)$, where $\tau_l : E(\mathbb{F}_l)[p] \times E(\mathbb{F}_l)/p \to \mathbb{F}_l^\times/(\mathbb{F}_l^\times)^p$ is the Tate–Lichtenbaum pairing (definition `Rank2Sha_TatePairing`). The **tame discriminant** is
--
--   $$
--   M(l_1, l_2) = h_{l_1}(P_1,P_1)\,h_{l_2}(P_2,P_2) + h_{l_1}(P_2,P_2)\,h_{l_2}(P_1,P_1) - 2\,h_{l_1}(P_1,P_2)\,h_{l_2}(P_1,P_2) \ \in \mathbb{F}_p .
--   $$
--
--   $M(l_1,l_2)$ does not depend on the choice of basis of $E(\mathbb{Q})$, and $\delta_{l_1l_2}$ and $M(l_1,l_2)$ change by the same factor in $\mathbb{F}_p^\times$ when $\eta_l$ is replaced by another primitive root.
--
--   **Formalization Note** $E(\mathbb{F}_l)$ is the type of points of the Weierstrass curve `curve389a1Mod l` over `ZMod l`, with Mathlib's group law; over $\mathbb{Q}$ the same equation is `Rank2Sha.curve389a1`. Primality of $p$ and $l$ is an instance argument `[Fact p.Prime]`. In `IsKolyvaginPrime p l` the condition on $E(\mathbb{F}_l)[p]$ is `Nat.card {P // p • P = 0} = p`. The pairing is evaluated with the auxiliary point $R = 0$ when that is admissible, and otherwise with the first admissible point in a fixed enumeration of $E(\mathbb{F}_l)$; $h_l$ does not depend on this choice. All definitions are computable and were checked against PARI/GP: point counts, primitive roots, the values $h_l$, $\delta_{l_1l_2}$ and $M(l_1,l_2)$.
-- source:
--   C.-H. Kim, The structure of Selmer groups and the Iwasawa main conjecture for elliptic curves, Amer. J. Math. 148 (2026), arXiv:2203.12159v6, Sections 1.4 and 1.5 (Kurihara numbers delta_n, normalisation) ; M. Kurihara, Refined Iwasawa theory for p-adic representations and the structure of Selmer groups, Münster J. Math. 7 (2014) ; B. Mazur, J. Tate, Refined conjectures of the "Birch and Swinnerton-Dyer type", Duke Math. J. 54 (1987), 711-750 (the tame pairing) ; https://www.lmfdb.org/EllipticCurve/Q/389/a/1

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.OfMap
import Definitions.Def_Rank2Sha_Curves
import Definitions.Def_Rank2Sha_PlusSymbol389
import Definitions.Def_Rank2Sha_TatePairing

/-!
# Kolyvagin primes, Kurihara numbers and the tame discriminant of 389a1

Let `E` be the curve `y² + y = x³ + x² - 2x` (LMFDB 389.a1), `P₁ = (0, 0)` and
`P₂ = (-1, 1)`, a basis of `E(ℚ)`. Let `p` be a prime. For a prime `l ≠ 389` write
`E(𝔽_l)` for the points of the reduction, `N_l = #E(𝔽_l)` and `P̄` for the reduction of `P`.

* `l` is a **Kolyvagin prime** for `p` if `l ≡ 1 (mod p)` and `E(𝔽_l)[p]` has exactly `p`
  elements, that is, `E(𝔽_l)[p]` is cyclic of order `p`.
* `η_l` is the least primitive root modulo `l`, and `λ_l(a) ∈ 𝔽_p` is the discrete
  logarithm of `a` to the base `η_l`, reduced modulo `p`.
* For distinct Kolyvagin primes `l₁, l₂` the **Kurihara number** is
      δ_{l₁l₂} = ∑_{a ∈ (ℤ/l₁l₂ℤ)^×} [a/(l₁l₂)]⁺ λ_{l₁}(a) λ_{l₂}(a)  ∈ 𝔽_p,
  with `[r]⁺` the plus modular symbol normalised by `Ω⁺ = ∫_{E(ℝ)} |ω|`
  (`Rank2Sha.plusModularSymbol389`).
* `h_l(P, Q) = λ_l(τ_l((N_l/p) P̄, Q̄))`, with `τ_l` the Tate–Lichtenbaum pairing
  `E(𝔽_l)[p] × E(𝔽_l)/p → 𝔽_l^×/(𝔽_l^×)^p`, and the **tame discriminant**
      M(l₁, l₂) = h_{l₁}(P₁,P₁) h_{l₂}(P₂,P₂) + h_{l₁}(P₂,P₂) h_{l₂}(P₁,P₁)
                  - 2 h_{l₁}(P₁,P₂) h_{l₂}(P₁,P₂)  ∈ 𝔽_p.

`M(l₁, l₂)` does not depend on the basis of `E(ℚ)` (a change of basis multiplies the
determinant it contains by `±1`), and `δ` and `M` change by the same factor when `η_l` is
replaced by another primitive root.

The pairing is evaluated by Miller functions (`Rank2Sha.tatePairingWith`) on the divisor
`(Q̄ + R) - (R)`, with `R = 0` when this is admissible and otherwise the first admissible
point in the order of `pointList389`. The value of `h_l` does not depend on that choice.

**Formalization Note** Points of the reduction are points of the Weierstrass curve
`curve389a1Mod l` over `ZMod l`, with the group law of Mathlib; it is the reduction of
`Rank2Sha.curve389a1` (`curve389a1Over_rat`). The reductions of `P₁, P₂` are the points with
the same coordinates. The definitions are computable. The statements that `δ_{l₁l₂}` is the
Kurihara number of the literature and `M` the expression above rest on
`Rank2Sha.plusModularSymbol389` and on the facts about Miller functions recorded in the file
`Rank2Sha_TatePairing`; they were checked numerically against PARI/GP and Sage.
-/

namespace Rank2Sha

open WeierstrassCurve WeierstrassCurve.Affine

/-- The Weierstrass equation `y² + y = x³ + x² - 2x` of 389a1 over a commutative ring `R`. -/
def curve389a1Over (R : Type*) [CommRing R] : WeierstrassCurve.Affine R := ⟨0, 1, 1, -2, 0⟩

/-- Over `ℚ` the equation is `Rank2Sha.curve389a1`. -/
theorem curve389a1Over_rat : curve389a1Over ℚ = curve389a1 := rfl

/-- The reduction of 389a1 modulo `l`, over `ZMod l`. -/
abbrev curve389a1Mod (l : ℕ) : WeierstrassCurve.Affine (ZMod l) := curve389a1Over (ZMod l)

/-- Nonsingularity of an affine point of `curve389a1Mod l` is decided by its explicit
equations. -/
instance (l : ℕ) (x y : ZMod l) : Decidable ((curve389a1Mod l).Nonsingular x y) :=
  decidable_of_iff' _ ((nonsingular_iff x y).trans (and_congr_left' (equation_iff x y)))

/-- The points of `curve389a1Mod l`: `0`, then the nonsingular affine points `(x, y)`,
`x, y ∈ {0, …, l - 1}`, in lexicographic order of `(x, y)`. -/
def pointList389 (l : ℕ) : List (curve389a1Mod l).Point :=
  .zero :: (List.range l).flatMap fun (x : ℕ) => (List.range l).filterMap fun (y : ℕ) =>
    if h : (curve389a1Mod l).Nonsingular (x : ZMod l) (y : ZMod l) then some (.some _ _ h)
    else none

/-- Every point of `curve389a1Mod l` occurs in `pointList389 l`. -/
theorem mem_pointList389 (l : ℕ) [NeZero l] (P : (curve389a1Mod l).Point) :
    P ∈ pointList389 l := by
  rcases P with _ | ⟨x, y, h⟩
  · exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨x.val, List.mem_range.2 (ZMod.val_lt x),
      List.mem_filterMap.2 ⟨y.val, List.mem_range.2 (ZMod.val_lt y), ?_⟩⟩)
    simp only [ZMod.natCast_zmod_val, dif_pos h]

/-- A prime is nonzero. -/
instance instNeZeroOfFactPrime (l : ℕ) [Fact l.Prime] : NeZero l :=
  ⟨(Fact.out : l.Prime).ne_zero⟩

/-- The finite set of points of `curve389a1Mod l`, from `pointList389`. -/
instance (l : ℕ) [NeZero l] : Fintype (curve389a1Mod l).Point :=
  Fintype.ofList (pointList389 l) (mem_pointList389 l)

theorem curve389a1Over_nonsingular_zero_zero (R : Type*) [CommRing R] [Nontrivial R] :
    (curve389a1Over R).Nonsingular 0 0 := by
  rw [nonsingular_iff, equation_iff]
  refine ⟨by simp [curve389a1Over], Or.inr ?_⟩
  simp [curve389a1Over]

theorem curve389a1Over_nonsingular_neg_one_one (R : Type*) [CommRing R] [Nontrivial R] :
    (curve389a1Over R).Nonsingular (-1) 1 := by
  rw [nonsingular_iff, equation_iff]
  refine ⟨by simp [curve389a1Over]; ring, Or.inl ?_⟩
  simp [curve389a1Over]
  ring_nf
  simp

/-- The reduction modulo `l` of `P₁ = (0, 0)`. -/
def reducedP₁ (l : ℕ) [Fact l.Prime] : (curve389a1Mod l).Point :=
  .some 0 0 (curve389a1Over_nonsingular_zero_zero (ZMod l))

/-- The reduction modulo `l` of `P₂ = (-1, 1)`. -/
def reducedP₂ (l : ℕ) [Fact l.Prime] : (curve389a1Mod l).Point :=
  .some (-1) 1 (curve389a1Over_nonsingular_neg_one_one (ZMod l))

/-- `l` is a Kolyvagin prime for `p` (for 389a1): `l ≠ 389`, `l ≡ 1 (mod p)`, and the
`p`-torsion of `E(𝔽_l)` has exactly `p` elements. -/
def IsKolyvaginPrime (p l : ℕ) [Fact l.Prime] : Prop :=
  l ≠ 389 ∧ l % p = 1 ∧ Nat.card {P : (curve389a1Mod l).Point // p • P = 0} = p

/-- The list `g⁰, g¹, …, g^(l-2)` modulo `l`. -/
def powersMod (l g : ℕ) : List ℕ := List.iterate (fun x => x * g % l) (1 % l) (l - 1)

/-- The least primitive root modulo the prime `l`: the least `g ∈ {1, …, l - 1}` with
`g^k ≢ 1 (mod l)` for `0 < k < l - 1`. -/
def leastPrimitiveRoot (l : ℕ) : ℕ :=
  ((List.range' 1 (l - 1)).find? fun g => !((powersMod l g).tail.contains 1)).getD 0

/-- The table of `λ_l` modulo `p`: the entry at `η_l^k mod l` is `k mod p`, for
`0 ≤ k < l - 1`, `η_l = leastPrimitiveRoot l`; the entry at `0` is `0`. -/
def tameLogTable (p l : ℕ) : Array (ZMod p) :=
  (powersMod l (leastPrimitiveRoot l)).zipIdx.foldl (fun T xk => T.set! xk.1 (xk.2 : ZMod p))
    (Array.replicate l 0)

/-- The tame logarithm `λ_l(a) ∈ ZMod p`: the discrete logarithm of `a` modulo `l` to the base
`leastPrimitiveRoot l`, reduced modulo `p`; its value at multiples of `l` is `0`. -/
def tameLog (p l a : ℕ) : ZMod p := (tameLogTable p l).getD (a % l) 0

/-- The Kurihara number `δ_{l₁l₂} = ∑_{a ∈ (ℤ/l₁l₂ℤ)^×} [a/(l₁l₂)]⁺ λ_{l₁}(a) λ_{l₂}(a)` in
`ZMod p`, for 389a1. -/
def kuriharaNumber389 (p l₁ l₂ : ℕ) [Fact p.Prime] : ZMod p :=
  let t₁ := tameLogTable p l₁
  let t₂ := tameLogTable p l₂
  ∑ a ∈ (Finset.range (l₁ * l₂)).filter (fun a => Nat.Coprime a (l₁ * l₂)),
    (plusModularSymbol389 ((a : ℚ) / ((l₁ * l₂ : ℕ) : ℚ)) : ZMod p) *
      t₁.getD (a % l₁) 0 * t₂.getD (a % l₂) 0

/-- `N_l = #E(𝔽_l)`. -/
def pointCount389 (l : ℕ) [Fact l.Prime] : ℕ := Fintype.card (curve389a1Mod l).Point

/-- The auxiliary point for the pairing at `(A, Q)`: the first point `R` of `pointList389 l`
that is admissible (`IsAdmissibleAuxiliary p A Q R`). The first point of the list is `0`, which
is admissible when `Q ∉ ⟨A⟩`; that case is tested first, so that the list is built only when
`Q ∈ ⟨A⟩`. If no point is admissible the value is `0`; this does not happen when `p • A = 0`
and `E(𝔽_l) ≠ ⟨A⟩`, in particular for `A ∈ E(𝔽_l)[p]` at a Kolyvagin prime `l`. -/
def auxiliaryPoint389 (p l : ℕ) [Fact l.Prime] (A Q : (curve389a1Mod l).Point) :
    (curve389a1Mod l).Point :=
  if IsAdmissibleAuxiliary p A Q 0 then 0 else
    ((pointList389 l).find? fun R => decide (IsAdmissibleAuxiliary p A Q R)).getD 0

/-- `λ_l(τ_l(A, Q)) ∈ ZMod p` for `A ∈ E(𝔽_l)[p]` and `Q ∈ E(𝔽_l)`, `τ_l` the
Tate–Lichtenbaum pairing for `p`. -/
def tameTatePairing389 (p l : ℕ) [Fact l.Prime] (A Q : (curve389a1Mod l).Point) : ZMod p :=
  tameLog p l (tatePairingWith p A Q (auxiliaryPoint389 p l A Q)).val

/-- `h_l(P, Q) = λ_l(τ_l((N_l/p) P, Q))`. -/
def tameHeight389 (p l : ℕ) [Fact l.Prime] (P Q : (curve389a1Mod l).Point) : ZMod p :=
  tameTatePairing389 p l ((pointCount389 l / p) • P) Q

/-- The tame discriminant `M(l₁, l₂) = h₁(P₁,P₁) h₂(P₂,P₂) + h₁(P₂,P₂) h₂(P₁,P₁)
- 2 h₁(P₁,P₂) h₂(P₁,P₂)`, `h_i = h_{l_i}`, for 389a1 and its basis `P₁ = (0,0)`,
`P₂ = (-1,1)`. -/
def tameDiscriminant389 (p l₁ l₂ : ℕ) [Fact l₁.Prime] [Fact l₂.Prime] : ZMod p :=
  let N₁ := pointCount389 l₁
  let N₂ := pointCount389 l₂
  let h₁ := fun P Q => tameTatePairing389 p l₁ ((N₁ / p) • P) Q
  let h₂ := fun P Q => tameTatePairing389 p l₂ ((N₂ / p) • P) Q
  h₁ (reducedP₁ l₁) (reducedP₁ l₁) * h₂ (reducedP₂ l₂) (reducedP₂ l₂)
    + h₁ (reducedP₂ l₁) (reducedP₂ l₁) * h₂ (reducedP₁ l₂) (reducedP₁ l₂)
    - 2 * h₁ (reducedP₁ l₁) (reducedP₂ l₁) * h₂ (reducedP₁ l₂) (reducedP₂ l₂)

/-- `tameDiscriminant389` is the formula of `M(l₁, l₂)` in the values `h_{l_i} = tameHeight389`;
the definition computes each `N_{l_i}` once. -/
theorem tameDiscriminant389_eq (p l₁ l₂ : ℕ) [Fact l₁.Prime] [Fact l₂.Prime] :
    tameDiscriminant389 p l₁ l₂ =
      tameHeight389 p l₁ (reducedP₁ l₁) (reducedP₁ l₁) *
          tameHeight389 p l₂ (reducedP₂ l₂) (reducedP₂ l₂)
        + tameHeight389 p l₁ (reducedP₂ l₁) (reducedP₂ l₁) *
          tameHeight389 p l₂ (reducedP₁ l₂) (reducedP₁ l₂)
        - 2 * tameHeight389 p l₁ (reducedP₁ l₁) (reducedP₂ l₁) *
          tameHeight389 p l₂ (reducedP₁ l₂) (reducedP₂ l₂) := rfl

end Rank2Sha


