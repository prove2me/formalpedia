-- Prove2me | Definitions.Def_MonoTestDAG_alg1
-- name    : MonoTestDAG_alg1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:10:40.986811+00:00
-- url     : https://prove2.me/theorems/02eb8185-d162-427d-af35-d12f37124934
-- title:
--   Algorithm 1: tester combining edge and vertex sampling
-- statement:
--   Run on a DAG $G=(V,E)$ with proximity parameter $\varepsilon$ and with $q=\lfloor C\,m^{1/3}/\varepsilon^{2/3}\rfloor$:
--
--   1. sample a multiset $S_E$ of $q$ edges independently and uniformly from $E$;
--   2. independently of each other and of $S_E$, sample two multisets $Q_L,Q_R$ of $q$ vertices uniformly with replacement;
--   3. query $f$ on every vertex of $Q_L\cup Q_R$ and every endpoint of an edge in $S_E$;
--   4. reject if some $(u,v)\in S_E$ has $f(u)>f(v)$;
--   5. reject if there are $x\in Q_L$, $y\in Q_R$ with $(x,y)\in E(\mathrm{TC}(G))$ and $f(x)>f(y)$;
--   6. otherwise accept.
--
--   **Formalization Note.** The page's "$q\leftarrow\Theta(m^{1/3}/\varepsilon^{2/3})$" is the floor of $C\,m^{1/3}/\varepsilon^{2/3}$ for a parameter $C$. When $m=0$ this is $0$, so nothing is sampled from an empty set. The seed is uniform on $E^q\times V^q\times V^q$ with the discrete σ-algebra. The module also defines `EdgeT`, `alg1Size`, `Alg1Seed` and `alg1Query`.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Algorithm 1, p.12

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_numTC
import Definitions.Def_MonoTestDAG_numTR

namespace MonoTestDAG

open MeasureTheory

/-- The edges `(u, v)` of `E`, as a type (the population Algorithm 1 samples from). -/
def EdgeT {V : Type} (E : V → V → Prop) : Type :=
  {p : V × V // E p.1 p.2}

noncomputable instance {V : Type} [Fintype V] (E : V → V → Prop) : Fintype (EdgeT E) := by
  classical
  unfold EdgeT
  infer_instance

/-- The sample size `q = ⌊C · m^{1/3} / ε^{2/3}⌋` of Algorithm 1, line 2 (`q ← Θ(m^{1/3}/ε^{2/3})`).
Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Algorithm 1, p.12. -/
noncomputable def alg1Size {V : Type} [Fintype V] (E : V → V → Prop) (C ε : ℝ) : ℕ :=
  ⌊C * (numTR E : ℝ) ^ ((1 : ℝ) / 3) / ε ^ ((2 : ℝ) / 3)⌋₊

/-- The seed space of Algorithm 1: `q` edges `S_E`, and two `q`-tuples of vertices `Q_L`, `Q_R`. -/
abbrev Alg1Seed {V : Type} [Fintype V] (E : V → V → Prop) (C ε : ℝ) : Type :=
  (Fin (alg1Size E C ε) → EdgeT E) × (Fin (alg1Size E C ε) → V) × (Fin (alg1Size E C ε) → V)

/-- A nonzero sample size forces an edge to exist (since `m = 0` gives `q = 0`), so the seed
space of Algorithm 1 is never empty. -/
theorem alg1Seed_nonempty {V : Type} [Fintype V] (E : V → V → Prop) (C ε : ℝ) :
    Nonempty (Alg1Seed E C ε) := by
  classical
  unfold Alg1Seed
  by_cases hq : alg1Size E C ε = 0
  · rw [hq]
    exact ⟨(fun i => i.elim0, fun i => i.elim0, fun i => i.elim0)⟩
  · have hm : numTR E ≠ 0 := by
      intro hm
      apply hq
      simp [alg1Size, hm]
    obtain ⟨p, hp⟩ := Finset.card_ne_zero.mp hm
    simp only [trPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hne, hreach, -⟩ := hp
    rcases Relation.ReflTransGen.cases_head hreach with h | ⟨w, hw, -⟩
    · exact absurd h hne
    · let e : EdgeT E := ⟨(p.1, w), hw⟩
      exact ⟨(fun _ => e, fun _ => p.1, fun _ => p.1)⟩

/-- The query set of Algorithm 1 (line 5): the vertices of `Q_L ∪ Q_R` and the endpoints of the
edges in `S_E`. -/
noncomputable def alg1Query {V : Type} [Fintype V] [DecidableEq V] (E : V → V → Prop) (C ε : ℝ)
    (ω : Alg1Seed E C ε) : Finset V :=
  (Finset.univ.image (fun i => (ω.1 i).1.1)) ∪ (Finset.univ.image (fun i => (ω.1 i).1.2)) ∪
    (Finset.univ.image ω.2.1) ∪ (Finset.univ.image ω.2.2)

theorem alg1Query_mem_src {V : Type} [Fintype V] [DecidableEq V] (E : V → V → Prop) (C ε : ℝ)
    (ω : Alg1Seed E C ε) (i : Fin (alg1Size E C ε)) : (ω.1 i).1.1 ∈ alg1Query E C ε ω := by
  simp only [alg1Query, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))

theorem alg1Query_mem_tgt {V : Type} [Fintype V] [DecidableEq V] (E : V → V → Prop) (C ε : ℝ)
    (ω : Alg1Seed E C ε) (i : Fin (alg1Size E C ε)) : (ω.1 i).1.2 ∈ alg1Query E C ε ω := by
  simp only [alg1Query, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))

theorem alg1Query_mem_left {V : Type} [Fintype V] [DecidableEq V] (E : V → V → Prop) (C ε : ℝ)
    (ω : Alg1Seed E C ε) (i : Fin (alg1Size E C ε)) : ω.2.1 i ∈ alg1Query E C ε ω := by
  simp only [alg1Query, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨i, rfl⟩)

theorem alg1Query_mem_right {V : Type} [Fintype V] [DecidableEq V] (E : V → V → Prop) (C ε : ℝ)
    (ω : Alg1Seed E C ε) (i : Fin (alg1Size E C ε)) : ω.2.2 i ∈ alg1Query E C ε ω := by
  simp only [alg1Query, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, rfl⟩

open Classical in
/-- **Algorithm 1** (tester combining edge and vertex sampling), run on the DAG `E` with
proximity parameter `ε` and sample size `q = alg1Size E C ε`:

1. sample a multiset `S_E` of `q` edges independently and uniformly from `E`;
2. independently, sample two multisets `Q_L`, `Q_R` of `q` vertices uniformly with replacement;
3. query `f` on `Q_L ∪ Q_R` and on every endpoint of an edge of `S_E`;
4. reject if some `(u, v) ∈ S_E` has `f(u) > f(v)`;
5. reject if some `x ∈ Q_L`, `y ∈ Q_R` have `(x, y) ∈ E(TC(G))` and `f(x) > f(y)`;
6. otherwise accept.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Algorithm 1, p.12.

**Formalization Note.** The seed is uniform on `(E^q) × (V^q) × (V^q)` (all coordinates
independent and uniform), with the discrete σ-algebra. "`q ← Θ(m^{1/3}/ε^{2/3})`" is the sample
size `⌊C m^{1/3}/ε^{2/3}⌋` for a constant `C`; when `m = 0` it is `0` and nothing is sampled. -/
noncomputable def alg1 {V : Type} [Fintype V] [DecidableEq V] (E : V → V → Prop) (C ε : ℝ) :
    Tester V :=
  haveI : Nonempty (Alg1Seed E C ε) := alg1Seed_nonempty E C ε
  letI : MeasurableSpace (Alg1Seed E C ε) := ⊤
  { Ω := Alg1Seed E C ε
    instMeas := ⊤
    P := (PMF.uniformOfFintype (Alg1Seed E C ε)).toMeasure
    isProb := inferInstance
    query := alg1Query E C ε
    rule := fun ω x =>
      decide ((¬ ∃ i, x ⟨(ω.1 i).1.2, alg1Query_mem_tgt E C ε ω i⟩ <
              x ⟨(ω.1 i).1.1, alg1Query_mem_src E C ε ω i⟩) ∧
        ¬ ∃ i j, (ω.2.1 i, ω.2.2 j) ∈ tcPairs E ∧
              x ⟨ω.2.2 j, alg1Query_mem_right E C ε ω j⟩ <
              x ⟨ω.2.1 i, alg1Query_mem_left E C ε ω i⟩)
    measurable_accept := fun _ => MeasurableSpace.measurableSet_top }

end MonoTestDAG


