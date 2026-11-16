-- Prove2me | Definitions.Def_BootstrapRecolorVerify_MetricGap_Supplement_Hierarchy
-- name    : BootstrapRecolorVerify_MetricGap_Supplement_Hierarchy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:29:01.10465+00:00
-- url     : https://prove2.me/theorems/8133bcad-777d-444c-9611-2b25fb2ecdf7
-- title:
--   Part I parameters, raw random lifts and exceptional sets
-- statement:
--   Fix an integer $r\ge2$ and a sufficiently large even integer $n$. Use natural logarithms and set
--
--   $$\eta=\frac1{r+1},\quad \beta_r=\frac1{30\,4^r\log(12r)},\quad L=\beta_r\log n,\quad \alpha=\frac{4^r\log(12r)}{\log n}.$$
--
--   Starting from one vertex, replace every old vertex by a cloud of $n_1=n^4$ vertices in the first stage and $n_i=n^{3\cdot4^{i-1}}$ vertices at stage $i\ge2$. Thus $N_i=n^{4^i}$. Add three independent uniform perfect matchings inside every new cloud and an independent uniform bijection above each individual old edge. Vertices retain their cloud coordinates and edges retain matching labels and descendant coordinates, including parallel edges. A history is the complete product of these independent choices, with no conditioning or rejection sampling; its raw event probability is the fraction of equally likely encodings satisfying the event.
--
--   At stage $i$, mark precisely the level-$i$ edges on simple cycles of at most $10L$ hops, including two distinct parallel edges. All and only descendants inherit those marks. The event of Claim 5.1 is
--
--   $$\forall j\in\{1,\ldots,r\},\qquad \frac{|F_j(G_r)|L^2}{N_r}\le\frac1n.$$
--
--   This module supplies the actual Part I random objects and ancestor projections shared by the added statements.
--
--   **Formalization Note** Internal matchings use consecutive pairs in uniform permutations. Every perfect matching has the same $2^{s/2}(s/2)!$ encodings, so this preserves the law. The published general undirected multigraph walk/cycle interface is reused with edge identities. No integer restriction is placed on $L$ or $L^\eta$.
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), §3, parameters (1), expanded lifts and exceptional sets; Claim 5.1 event, p.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=6; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_PoSUndirected_IsSimplePathEdges

open scoped Classical

namespace BootstrapRecolorVerify.MetricGap.Supplement

/-- Part I, §3 pp.5--6. This scale is real, with no integer restriction. -/
noncomputable def eta (r : ℕ) : ℝ := 1 / ((r : ℝ) + 1)
noncomputable def beta (r : ℕ) : ℝ := 1 / (30 * (4 : ℝ) ^ r * Real.log (12 * r))
noncomputable def lengthScale (r n : ℕ) : ℝ := beta r * Real.log n
noncomputable def sparsityAlpha (r n : ℕ) : ℝ := (4 : ℝ) ^ r * Real.log (12 * r) / Real.log n

def cloudSize (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => n ^ 4
  | i + 2 => n ^ (3 * 4 ^ (i + 1))

/-- Successive cloud coordinates; the level-zero graph is one vertex. -/
def Vertex (n : ℕ) : ℕ → Type
  | 0 => Unit
  | i + 1 => Vertex n i × Fin (cloudSize n (i + 1))

instance vertexFintype (n : ℕ) : (i : ℕ) → Fintype (Vertex n i)
  | 0 => inferInstanceAs (Fintype Unit)
  | i + 1 => @instFintypeProd _ _ (vertexFintype n i) inferInstance

/-- Distinct labels retain parallel edges and every descendant. -/
def Edge (n : ℕ) : ℕ → Type
  | 0 => Empty
  | i + 1 => (Edge n i × Fin (cloudSize n (i + 1))) ⊕
      (Vertex n i × Fin 3 × Fin (cloudSize n (i + 1) / 2))

instance edgeFintype (n : ℕ) : (i : ℕ) → Fintype (Edge n i)
  | 0 => inferInstanceAs (Fintype Empty)
  | i + 1 => by
      letI := edgeFintype n i
      change Fintype ((_ × _) ⊕ (_ × _ × _))
      infer_instance

/-- Pairing consecutive positions of a uniform permutation gives a uniform
perfect matching when the cloud size is even. Every matching has exactly
2^(s/2)(s/2)! encodings. The redundant encoding retains the source's law. -/
abbrev InternalArray (n i : ℕ) :=
  Vertex n i → Fin 3 → Equiv.Perm (Fin (cloudSize n (i + 1)))
abbrev LiftArray (n i : ℕ) := Edge n i → Equiv.Perm (Fin (cloudSize n (i + 1)))
abbrev Stage (n i : ℕ) := InternalArray n i × LiftArray n i

/-- The complete RAW product of independent uniform matching encodings. No
acceptance event, graph property, metric inequality or gap is a field. -/
def History (n : ℕ) : ℕ → Type
  | 0 => Unit
  | i + 1 => History n i × Stage n i

noncomputable instance historyFintype (n : ℕ) : (i : ℕ) → Fintype (History n i)
  | 0 => inferInstanceAs (Fintype Unit)
  | i + 1 => by
      letI := historyFintype n i
      change Fintype (_ × _)
      infer_instance

/-- Raw probability, counting complete matching encodings equally. The sample
space is always nonempty (identity permutations provide one history). -/
noncomputable def rawProbability {n i : ℕ} (P : History n i → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / Fintype.card (History n i)

def evenPosition {s : ℕ} (a : Fin (s / 2)) : Fin s := ⟨2 * a.val, by omega⟩
def oddPosition {s : ℕ} (a : Fin (s / 2)) : Fin s := ⟨2 * a.val + 1, by omega⟩

def endpoints {n : ℕ} : {i : ℕ} → History n i → Edge n i → Vertex n i × Vertex n i
  | 0, _, e => Empty.elim e
  | _ + 1, H, Sum.inl (e, a) =>
      let uv := endpoints H.1 e
      ((uv.1, a), (uv.2, H.2.2 e a))
  | _ + 1, H, Sum.inr (u, label, a) =>
      let p := H.2.1 u label
      ((u, p (evenPosition a)), (u, p (oddPosition a)))

/-- The published general multigraph interface, with individual edge identities. -/
def ends {n i : ℕ} (H : History n i) (e : Edge n i) : Sym2 (Vertex n i) :=
  s((endpoints H e).1, (endpoints H e).2)

def edgeLevel {n : ℕ} : {i : ℕ} → Edge n i → ℕ
  | 0, e => Empty.elim e
  | _ + 1, Sum.inl (e, _) => edgeLevel e
  | i + 1, Sum.inr _ => i + 1

def project (n : ℕ) : {i : ℕ} → (j : ℕ) → j ≤ i → Vertex n i → Vertex n j
  | i, j, h, v =>
      if he : j = i then he ▸ v
      else match i with
        | 0 => False.elim (by omega)
        | _ + 1 => project n j (by omega) v.1

def historyPrefix (n : ℕ) : {i : ℕ} → (j : ℕ) → j ≤ i → History n i → History n j
  | i, j, h, H =>
      if he : j = i then he ▸ H
      else match i with
        | 0 => False.elim (by omega)
        | _ + 1 => historyPrefix n j (by omega) H.1

/-- Simple cycles may use all levels; two parallel edges count as a cycle.
The published cycle predicate also allows loops, which this construction never has. -/
def OnShortCycle {n i : ℕ} (r : ℕ) (H : History n i) (e : Edge n i) : Prop :=
  ∃ C : Finset (Edge n i), e ∈ C ∧ PoSUndirected.IsCycleEdges (ends H) C ∧
    (C.card : ℝ) ≤ 10 * lengthScale r n

/-- Mark only newly created edges, then inherit their marks. Older edges are
NEVER newly marked, and dense-subgraph marking is absent in Part I. -/
def Exceptional {n : ℕ} (r : ℕ) : {i : ℕ} → History n i → Edge n i → Prop
  | 0, _, e => Empty.elim e
  | _ + 1, H, Sum.inl (e, _) => Exceptional r H.1 e
  | _ + 1, H, e@(Sum.inr _) => OnShortCycle r H e

/-- The exact simultaneous event of Claim 5.1, with each level counted separately. -/
def ExceptionalEvent {n r : ℕ} (H : History n r) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ r →
    (((Finset.univ.filter fun e : Edge n r => edgeLevel e = j ∧ Exceptional r H e).card : ℝ) *
      lengthScale r n ^ 2) / Fintype.card (Vertex n r) ≤ 1 / (n : ℝ)

end BootstrapRecolorVerify.MetricGap.Supplement


