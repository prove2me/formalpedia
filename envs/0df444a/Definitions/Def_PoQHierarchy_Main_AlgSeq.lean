-- Prove2me | Definitions.Def_PoQHierarchy_Main_AlgSeq
-- name    : PoQHierarchy_Main_AlgSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:49.394578+00:00
-- url     : https://prove2.me/theorems/1fdca9bb-256c-4540-be40-f1275d7cc2d1
-- title:
--   $n$-partite $I$-quantum algebraic sequential strategies (Definition 5.6)
-- statement:
--   An **$n$-partite $I$-quantum algebraic sequential strategy** (Definition 5.6) consists of
--
--   1. unital C*-algebras $\mathcal A_0,\dots,\mathcal A_n$;
--   2. a state $\phi:\mathcal A_0\to\mathbb C$ (a positive linear functional with $\phi(1)=1$);
--   3. for every player $i\in[n]$ and question $x\in I_i$, a quantum instrument of subunital completely positive maps $T^{(i)}_{a|x}:\mathcal A_i\to\mathcal A_{i-1}$, $a\in O_i$, such that $T^{(i)}_x=\sum_aT^{(i)}_{a|x}$ is unital;
--   4. for every $i\notin I$, a family of subunital completely positive maps $S^{(i)}_\lambda:\mathcal A_i\to\mathcal A_{i-1}$, $\lambda\in O_i^{I_i}$, with $T^{(i)}_{a|x}=\sum_{\lambda:\lambda(x)=a}S^{(i)}_\lambda$.
--
--   The strategy is **operational non-signaling** if $\sum_aT^{(i)}_{a|x}$ is independent of $x$ for every player. Its correlation is
--   $$\Pr[a_1,\dots,a_n\mid x_1,\dots,x_n]=\phi\circ T^{(1)}_{a_1|x_1}\circ\cdots\circ T^{(n)}_{a_n|x_n}(1_{\mathcal A_n}).$$
--
--   The players outside $I$ use classically compatible instruments: they act as if they first measured an entire response function $\lambda$.
--
--   **Formalization Note** The algebras are Mathlib's `CStarAlgebra`s, each with its C*-order given as a partial order making it a star-ordered ring (so that $0\le a$ means that $a$ is positive), and the maps are Mathlib's completely positive maps.
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), §5.3, Definition 5.6 (p.31); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_Basic

open QAlgorithms.Complexity
open scoped ComplexOrder CStarAlgebra
set_option autoImplicit false

namespace PoQHierarchy.Main

/-!
Bacho, Leichtle, Arora, Cojocaru, STOC 2027 submission #1666, §5.3, Definition 5.6 (p.31):
`n`-partite `I`-quantum algebraic sequential strategies.

The algebras are unital C*-algebras (Mathlib's `CStarAlgebra`) with their C*-order (a partial
order making them star-ordered rings, so that `0 ≤ a` means `a` is positive); the instruments are
Mathlib's completely positive maps `A_i →CP A_{i-1}`. Player `i` (written `i : Fin n`, i.e. the
paper's player `i+1`) maps `A_{i+1}` to `A_i`.
-/

/-- An **`n`-partite `I`-quantum algebraic sequential strategy** (Definition 5.6) for question sets
`Fin (q i)` and answer sets `Fin (o i)`: unital C*-algebras `A_0, …, A_n`; a state `ϕ` on `A_0`
(a positive linear functional with `ϕ(1) = 1`); for every player and question an instrument of
subunital CP maps `T^{(i)}_{a|x} : A_i → A_{i-1}` whose sum over `a` is unital; and for every player
outside `I` a family of subunital CP maps `S^{(i)}_λ`, `λ ∈ O_i^{I_i}`, with
`T^{(i)}_{a|x} = ∑_{λ : λ(x) = a} S^{(i)}_λ`. -/
structure AlgSeqStrategy (n : ℕ) (q o : Fin n → ℕ) (I : Finset (Fin n)) where
  A : Fin (n + 1) → Type
  [cstar : ∀ j, CStarAlgebra (A j)]
  [po : ∀ j, PartialOrder (A j)]
  [sor : ∀ j, StarOrderedRing (A j)]
  ϕ : A 0 →ₗ[ℂ] ℂ
  ϕ_pos : ∀ a : A 0, 0 ≤ a → 0 ≤ ϕ a
  ϕ_one : ϕ 1 = 1
  T : (i : Fin n) → Fin (q i) → Fin (o i) → (A i.succ →CP A i.castSucc)
  T_subunital : ∀ i x a, T i x a 1 ≤ 1
  T_unital : ∀ i x, ∑ a, T i x a 1 = 1
  S : (i : Fin n) → i ∉ I → (Fin (q i) → Fin (o i)) → (A i.succ →CP A i.castSucc)
  S_subunital : ∀ i (h : i ∉ I) l, S i h l 1 ≤ 1
  T_parent : ∀ i (h : i ∉ I) x a,
    (T i x a).toLinearMap =
      ∑ l ∈ Finset.univ.filter (fun l : Fin (q i) → Fin (o i) => l x = a), (S i h l).toLinearMap

attribute [instance] AlgSeqStrategy.cstar AlgSeqStrategy.po AlgSeqStrategy.sor

/-- The strategy is **operational non-signaling** (p.31): for every player, the map
`T^{(i)}_x = ∑_a T^{(i)}_{a|x}` does not depend on the question `x`. -/
def AlgSeqStrategy.OperationalNS {n : ℕ} {q o : Fin n → ℕ} {I : Finset (Fin n)}
    (St : AlgSeqStrategy n q o I) : Prop :=
  ∀ i x x', ∑ a, (St.T i x a).toLinearMap = ∑ a, (St.T i x' a).toLinearMap

/-- The element `T^{(j+1)}_{a_{j+1}|x_{j+1}} ∘ ⋯ ∘ T^{(n)}_{a_n|x_n}(1_{A_n}) ∈ A_j`. -/
noncomputable def AlgSeqStrategy.chain {n : ℕ} {q o : Fin n → ℕ} {I : Finset (Fin n)}
    (St : AlgSeqStrategy n q o I) (a : (i : Fin n) → Fin (o i)) (x : (i : Fin n) → Fin (q i))
    (j : Fin (n + 1)) : St.A j :=
  Fin.reverseInduction (motive := fun j => St.A j) (1 : St.A (Fin.last n))
    (fun i v => St.T i (x i) (a i) v) j

/-- The correlation `Pr[a|x] = ϕ ∘ T^{(1)}_{a_1|x_1} ∘ ⋯ ∘ T^{(n)}_{a_n|x_n}(1_{A_n})` (p.31). -/
noncomputable def AlgSeqStrategy.corr {n : ℕ} {q o : Fin n → ℕ} {I : Finset (Fin n)}
    (St : AlgSeqStrategy n q o I) (a : (i : Fin n) → Fin (o i)) (x : (i : Fin n) → Fin (q i)) : ℂ :=
  St.ϕ (St.chain a x 0)

end PoQHierarchy.Main


