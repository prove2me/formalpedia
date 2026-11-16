-- Prove2me | Definitions.Def_SemAC02_Supplement_IsSemPCRef
-- name    : SemAC02_Supplement_IsSemPCRef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:40:25.224239+00:00
-- url     : https://prove2.me/theorems/b1fcb936-918f-4f5c-8335-e091a6f2dd30
-- title:
--   Semantic C-PC refutations and the measures S(π), size(π), |π|₄, M_bot(π)
-- statement:
--   Let $\mathcal C$ be a class of algebraic circuits over a field $\mathbb F$, $\Omega\subseteq\{0,1\}^\sigma$ a domain and $\mathcal A$ a set of axioms (elements of $B_\sigma(\mathbb F)$). An **arity-2 semantic $\mathcal C$-PC refutation** on $\Omega$ is a sequence of circuits $P_1,\dots,P_L\in\mathcal C$ in which every line
--
--   1. agrees on $\Omega$ with an axiom, or
--   2. vanishes on $\Omega$ (an initial tautology $0=0$), or
--   3. follows from two earlier lines $P_i,P_j$ ($i=j$ allowed): $P_i(x)=P_j(x)=0\Rightarrow P_k(x)=0$ for every $x\in\Omega$,
--
--   and whose last line equals $1$ on $\Omega$. With $\Omega=\{0,1\}^\sigma$ this is semantic $\mathcal C$-PC; with $\Omega$ the zero set of background axioms $F_0$ it is a refutation modulo $F_0$ (inferences interpreted on $\Omega$).
--
--   The measures of a refutation $\pi$ are:
--
--   1. $S(\pi)$, the number of distinct non-zero top product terms of its lines, as elements of the Boolean quotient (functions on $\Omega$);
--   2. the $\mathcal C$-size $\mathrm{size}(\pi)$, the number of distinct rooted subcircuits anywhere in $\pi$, shared across lines;
--   3. $|\pi|_4=\sum_v|C_v|$, the sum over the lines of the sizes of their displayed circuits;
--   4. $M_{\mathrm{bot}}(\pi)$, the maximum of $1$ and the number of distinct monomials of the multilinear bottom polynomials;
--   5. the number of top product-term occurrences;
--   6. the degree of a line, the degree of its multilinear representative.
--
--   These notions state every lower and upper bound of §§2–7.
--
--   **Formalization Note** Axioms are given as functions on the cube (`polyAx` turns polynomials into such functions). An axiom line is any line whose value equals an axiom, since a line represents its residue class (p.15). Initial lines equal to $0$ follow the convention of p.54; they add no refutational power.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §2, pp.15–16 (PDF pp.17–18); §4, p.24 (PDF p.26); §7.3.1, pp.54–55 (PDF pp.56–57)

import Mathlib
import Definitions.Def_SemAC02_Supplement_ACirc

namespace SemAC02.Supplement

open MvPolynomial ACirc

/-- An **arity-2 semantic `C`-PC refutation** on a domain `Ω ⊆ {0,1}^σ` (Alekseev–Gryaznov–
Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript
(STOC 2027 submission), §2.2, p.16; §4, p.24; §7.3.1, p.54; Theorem 7.5, p.53): a sequence `π` of
circuits of the class `Cl` (the proof lines) such that every line `π[k]`

* agrees on `Ω` with an axiom `a ∈ Ax` (axioms are given as functions on the cube, i.e. as
  elements of `B_σ(F)`), or
* is zero on `Ω` (an initial tautology `0 = 0`, p.54), or
* is a semantic consequence on `Ω` of two earlier lines `π[i]`, `π[j]` (`i = j` allowed, which
  covers one-premise inferences): `P_i(x) = P_j(x) = 0 ⟹ P_k(x) = 0` for every `x ∈ Ω`;

and whose last line equals the constant `1` on `Ω` (the line `1 = 0`).

With `Ω = Set.univ` this is the semantic `C`-PC of p.16 ("for every `x ∈ {0,1}^n`"). With
`Ω` the zero set of background axioms `F₀` it is the refutation modulo `F₀` of §4 ("semantic
inferences are interpreted on `Ω`", p.24) and of the second part of Theorem 7.5.

**Formalization Note** A line is a displayed circuit; its value is its class `cval` in `B_σ(F)`
(p.15), so axiom lines are those whose class (on `Ω`) is an axiom. The size measures (`topS`,
`csize`, `size4`, `Mbot`, `topOcc`) read the displayed circuits. -/
def IsSemPCRef {F σ : Type} [Field F] (Cl : ACirc F σ → Prop) (Ω : Set (σ → Bool))
    (Ax : Set ((σ → Bool) → F)) (π : List (ACirc F σ)) : Prop :=
  (∀ c ∈ π, Cl c) ∧
  (∀ (k : ℕ) (hk : k < π.length),
    (∃ a ∈ Ax, ∀ x ∈ Ω, cval π[k] x = a x) ∨
    (∀ x ∈ Ω, cval π[k] x = 0) ∨
    (∃ (i j : ℕ) (hi : i < k) (hj : j < k), ∀ x ∈ Ω,
      cval (π[i]'(hi.trans hk)) x = 0 → cval (π[j]'(hj.trans hk)) x = 0 → cval π[k] x = 0)) ∧
  ∃ c, π.getLast? = some c ∧ ∀ x ∈ Ω, cval c x = 1

/-- The axioms given by a set of polynomials, as elements of `B_σ(F)`. -/
noncomputable def polyAx {F σ : Type} [CommRing F] (S : Set (MvPolynomial σ F)) :
    Set ((σ → Bool) → F) :=
  polyFn '' S

/-- **`S(π)`** on the domain `Ω` (p.15 and p.26): the number of distinct non-zero top product
terms of the proof, "identified as elements of the Boolean quotient". On `Ω = Set.univ` the
classes live in `B_σ(F)`; on the zero set `Ω` of background axioms `F₀` they are the classes in
`B_{F₀}` (Theorem 4.5, p.26: "the residue classes in `B_{F₀}` of the polynomials computed by
their top product gates"). -/
noncomputable def topS {F σ : Type} [CommRing F] (Ω : Set (σ → Bool)) (π : List (ACirc F σ)) :
    ℕ :=
  Set.ncard {g : Ω → F | g ≠ 0 ∧ ∃ c ∈ π, ∃ t ∈ topTerms c, g = fun x => cval t x.1}

/-- The **`C`-size** `size(π)` of a proof (p.15, item 3): "the number of distinct rooted subcircuits
appearing anywhere in `π`, allowing sharing across proof lines". -/
noncomputable def csize {F σ : Type} (π : List (ACirc F σ)) : ℕ :=
  open Classical in (π.toFinset.biUnion ACirc.subterms).card

/-- The total ΣΠΣΠ circuit size `|π|₄ = ∑_{v ∈ V(π)} |C_v|` (32), p.55: the sum over the proof
lines of the number of vertices of the displayed circuit (its distinct subcircuits). -/
noncomputable def size4 {F σ : Type} (π : List (ACirc F σ)) : ℕ :=
  (π.map (fun c => (ACirc.subterms c).card)).sum

/-- `M_bot(π)` (p.55): the maximum of `1` and the number of distinct monomials occurring in the
multilinear representatives of the bottom polynomials of `π`. -/
noncomputable def Mbot {F σ : Type} [CommRing F] (π : List (ACirc F σ)) : ℕ :=
  open Classical in
  max 1 (((π.flatMap ACirc.bottomPolys).toFinset.biUnion
    (fun b => (mlz b.toPoly).support)).card)

/-- The number of product-term occurrences of a proof (Theorem 7.9, p.56): the total number of
children of the top plus gates of its lines, counted with repetition. -/
def topOcc {F σ : Type} (π : List (ACirc F σ)) : ℕ :=
  (π.map (fun c => (ACirc.topTerms c).length)).sum

/-- The **degree** of an element `f` of `B_σ(F)` (p.15): the degree of its multilinear
representative, equivalently the least total degree of a polynomial representing `f`. -/
noncomputable def fnDeg {F σ : Type} [CommRing F] (f : (σ → Bool) → F) : ℕ :=
  sInf {d : ℕ | ∃ p : MvPolynomial σ F, p.totalDegree ≤ d ∧ polyFn p = f}

end SemAC02.Supplement


