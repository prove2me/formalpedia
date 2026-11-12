-- Prove2me | Definitions.Def_PoQHierarchy_Main_ICO
-- name    : PoQHierarchy_Main_ICO
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:34.073204+00:00
-- url     : https://prove2.me/theorems/6280368e-e485-4087-a90c-c30cceb179ce
-- title:
--   $I$-quantum commuting operator strategies (Definitions 5.1, 5.2) and the value $\omega_{qc\text{-}I}$
-- statement:
--   Fix $n$ players and $I\subseteq[n]$. An **$I$-quantum commuting operator strategy** (Definition 5.1) consists of a complex Hilbert space $\mathcal H$, possibly infinite-dimensional, a unit vector $|\Omega\rangle\in\mathcal H$, and for every player $i$ and question $x\in I_i$ a POVM $\{P^{(i)}_{xa}\}_{a\in O_i}$ of bounded positive operators on $\mathcal H$ summing to the identity, such that
--
--   1. (*commutation between distinct players*) $[P^{(i)}_{xa},P^{(j)}_{yb}]=0$ for all $i\ne j$ and all $x,a,y,b$;
--   2. (*classicality of players outside $I$*) $[P^{(i)}_{xa},P^{(i)}_{x'a'}]=0$ for every $i\notin I$ and all $x,a,x',a'$.
--
--   Its correlation is
--   $$\Pr[a_1,\dots,a_n\mid x_1,\dots,x_n]=\langle\Omega|\prod_{i=1}^nP^{(i)}_{x_ia_i}|\Omega\rangle,$$
--   the product taken in the order $i=1,\dots,n$. The value $\omega_{qc\text{-}I}(G)$ is the supremum of the winning probabilities of such strategies.
--
--   A family of POVMs $\{P_{xa}\}_{a\in O}$, $x\in X$, is **jointly measurable** (Definition 5.2) if there is a parent POVM $\{Q_\lambda\}_{\lambda\in O^X}$ with $P_{xa}=\sum_{\lambda:\lambda(x)=a}Q_\lambda$. The **generalized** $I$-quantum commuting operator strategy of p.28 replaces condition 2 by: for every $i\notin I$ the family $\{P^{(i)}_{xa}\}$ is jointly measurable with a parent POVM that commutes with every operator of every other player.
--
--   $I=\emptyset$ gives classical correlations and $I=[n]$ the commuting operator model; $\omega_{qc\text{-}I}$ interpolates between $\omega_c$ and $\omega_{qc}$.
--
--   **Formalization Note** The Hilbert space ranges over complex Hilbert spaces in Lean's lowest universe, which suffices because the finitely many operators of a strategy generate a separable cyclic subspace. Correlations are complex numbers (they are real); the winning probability uses their real part.
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), §5.1, Definition 5.1 (p.27), Definition 5.2 and the generalized definition (p.28); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_NonlocalGame

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-!
Bacho, Leichtle, Arora, Cojocaru, STOC 2027 submission #1666, §5.1 (pp.27–29): `I`-quantum
commuting operator strategies (Definition 5.1), joint measurability (Definition 5.2), the
generalized form of p.28, and the value `ω_{qc-I}(G)`.

The Hilbert space is any complex Hilbert space, possibly infinite-dimensional; operators are bounded
(`H →L[ℂ] H`). Strategies are described for question sets `Fin (q i)` and answer sets `Fin (o i)`,
so that the same notion serves a game and the games built from it.
-/

/-- An **`I`-quantum commuting operator strategy** (Definition 5.1) for `n` players with question
sets `Fin (q i)` and answer sets `Fin (o i)`: a complex Hilbert space `H`, a unit vector `Ω`, and for
every player `i` and question `x` a POVM `{P^{(i)}_{xa}}_a` on `H`, such that operators of distinct
players commute (*Commutation Between Distinct Players*) and the operators of each player outside
`I` commute among themselves (*Classicality of Players Outside I*). -/
structure ICOStrategy (n : ℕ) (q o : Fin n → ℕ) (I : Finset (Fin n)) where
  H : Type
  [nacg : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]
  Ω : H
  Ω_norm : ‖Ω‖ = 1
  P : (i : Fin n) → Fin (q i) → Fin (o i) → (H →L[ℂ] H)
  P_pos : ∀ i x a, (P i x a).IsPositive
  P_sum : ∀ i x, ∑ a, P i x a = 1
  comm_players : ∀ i j, i ≠ j → ∀ x a y b, Commute (P i x a) (P j y b)
  classical : ∀ i, i ∉ I → ∀ x a x' a', Commute (P i x a) (P i x' a')

attribute [instance] ICOStrategy.nacg ICOStrategy.ips ICOStrategy.cs

/-- The correlation `Pr[a_1, …, a_n | x_1, …, x_n] = ⟨Ω| ∏_{i=1}^n P^{(i)}_{x_i a_i} |Ω⟩`, the product
taken in the order `i = 1, …, n`. -/
noncomputable def ICOStrategy.corr {n : ℕ} {q o : Fin n → ℕ} {I : Finset (Fin n)}
    (S : ICOStrategy n q o I) (a : (i : Fin n) → Fin (o i)) (x : (i : Fin n) → Fin (q i)) : ℂ :=
  inner ℂ S.Ω ((((List.finRange n).map fun i => S.P i (x i) (a i)).prod) S.Ω)

/-- `Pr[S wins G]` for an `I`-quantum commuting operator strategy (the correlation is real; its real
part is taken). -/
noncomputable def ICOStrategy.win {n : ℕ} (G : NonlocalGame n) {I : Finset (Fin n)}
    (S : ICOStrategy n G.q G.o I) : ℝ :=
  G.winOf fun a x => (S.corr a x).re

/-- The value `ω_{qc-I}(G)` (p.27): the supremum of the winning probabilities of `I`-quantum
commuting operator strategies. -/
noncomputable def omegaQC {n : ℕ} (G : NonlocalGame n) (I : Finset (Fin n)) : ℝ :=
  sSup {v | ∃ S : ICOStrategy n G.q G.o I, S.win G = v}

/-- **Joint measurability** (Definition 5.2): a family of POVMs `{P_{xa}}_{a ∈ O}`, `x ∈ X`, has a
parent POVM `{Q_λ}_{λ ∈ O^X}` with `P_{xa} = ∑_{λ : λ(x) = a} Q_λ`. -/
def JointlyMeasurable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {X O : ℕ} (P : Fin X → Fin O → (H →L[ℂ] H)) (Q : (Fin X → Fin O) → (H →L[ℂ] H)) : Prop :=
  (∀ l, (Q l).IsPositive) ∧ ∑ l, Q l = 1 ∧
    ∀ x a, P x a = ∑ l ∈ Finset.univ.filter (fun l : Fin X → Fin O => l x = a), Q l

/-- The **generalized `I`-quantum commuting operator strategy** of p.28: as in Definition 5.1, but
for every player `i ∉ I` the family `{P^{(i)}_{xa}}` is only required to be jointly measurable, with
a parent POVM commuting with every operator of every other player. -/
structure GenICOStrategy (n : ℕ) (q o : Fin n → ℕ) (I : Finset (Fin n)) where
  H : Type
  [nacg : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]
  Ω : H
  Ω_norm : ‖Ω‖ = 1
  P : (i : Fin n) → Fin (q i) → Fin (o i) → (H →L[ℂ] H)
  P_pos : ∀ i x a, (P i x a).IsPositive
  P_sum : ∀ i x, ∑ a, P i x a = 1
  comm_players : ∀ i j, i ≠ j → ∀ x a y b, Commute (P i x a) (P j y b)
  parent : ∀ i, i ∉ I → ∃ Q : (Fin (q i) → Fin (o i)) → (H →L[ℂ] H),
    JointlyMeasurable (P i) Q ∧ ∀ l, ∀ j, j ≠ i → ∀ y b, Commute (Q l) (P j y b)

attribute [instance] GenICOStrategy.nacg GenICOStrategy.ips GenICOStrategy.cs

/-- The correlation of a generalized strategy, `⟨Ω| ∏_{i=1}^n P^{(i)}_{x_i a_i} |Ω⟩`. -/
noncomputable def GenICOStrategy.corr {n : ℕ} {q o : Fin n → ℕ} {I : Finset (Fin n)}
    (S : GenICOStrategy n q o I) (a : (i : Fin n) → Fin (o i)) (x : (i : Fin n) → Fin (q i)) : ℂ :=
  inner ℂ S.Ω ((((List.finRange n).map fun i => S.P i (x i) (a i)).prod) S.Ω)

end PoQHierarchy.Main


