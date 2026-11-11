-- Prove2me | Definitions.Def_WaitFreeTasks_Characterization_Refinement
-- name    : WaitFreeTasks_Characterization_Refinement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:29:41.920861+00:00
-- url     : https://prove2.me/theorems/12927276-ea35-453a-aa5d-8b1f76343fd0
-- title:
--   Stellar refinement, colorings, runs and the decision vertex relation
-- statement:
--   The initial color of a fine vertex is the minimum color in its output image carrier. A proper coloring is injective on every face, and a Sperner coloring uses only colors of the original input carrier. For a fixed map $f$, define
--
--   $$\operatorname{pre}_f^K(\Sigma)=\{\sigma\in K:f(|\sigma|)\subseteq|\Sigma|\}.$$
--
--   A violated edge has equal endpoint colors. A nonempty simplex is shallow if all its colors are below the output color indexed by its dimension; an out-of-range index gives false. Stellar subdivision replaces each containing face by the new interior vertex joined to the face with one selected vertex removed, together with all nonempty faces. The run relation implements the source's push-down loop followed by descending shatter loops, in nondecreasing output dimension, retaining old colors. Completed runs are finite sequences of these operations and loop exit tests; no invariant or existence theorem is a structure field. The decision map relation selects exactly the vertex of the image carrier having the assigned color. Its domain is the actual vertex subtype, including the empty case. Existence, uniqueness, simpliciality and carriedness are theorem conclusions.
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), pp. 6–7, 10–12, 16 (PDF pp. 8–9, 12–14, 18), Definitions 1–5 and §4.2 procedure

import Definitions.Def_WaitFreeTasks_Characterization_Task

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-! # Colourings of subdivisions, stellar subdivision, and the refinement procedure of §4.2

Attiya–Paz, STOC 2027 submission #828: Definition 1 (printed p. 6), §2.2 (Sperner, p. 7),
§4.1 Definition 2 (p. 10), §4.2 Definitions 3–4 and the procedure (pp. 11–12), §4.3
Definition 5 (p. 16).

Throughout, the vertices of a subdivision of `I` are points of the ambient space `ℝ^{V_I}` of
`|I|`, and a colouring is a function from these points to `Fin n` (identifier `i` ↦ `i - 1`);
only its values at the vertices matter. -/

/-- The property of the subdivision `div(I)` provided by Lemma 2 (§4.2, printed p. 10,
lines 403–404): on every simplex `σ` of `D` the map `f` is linear (affine in barycentric
coordinates) and `f(|σ|)` lies in the realization of a simplex of `O`. -/
def IsAdapted {n : ℕ} {VI VO : Type} (T : Task n VI VO) (f : (VI → ℝ) → (VO → ℝ))
    (D : GCx (VI → ℝ)) : Prop :=
  ∀ σ ∈ D.faces, AffineOnSimplex f σ ∧ ∃ τ ∈ T.O.faces, f '' gs σ ⊆ face τ

/-- **Definition 2** (printed p. 10): `col(v)` is the minimal colour in
`id_O(carr_O(f(|v|)))`. Guard: if that set were empty (it is not, at the vertices of a
subdivision of `I` when `f` maps `|I|` into `|O|`), the value is the identifier `0`. -/
noncomputable def initColor {n : ℕ} {VI VO : Type} (hn : 0 < n) (T : Task n VI VO)
    (f : (VI → ℝ) → (VO → ℝ)) : (VI → ℝ) → Fin n := fun v =>
  if h : ((carrOf T.O.faces {f v}).image T.idO).Nonempty then
    ((carrOf T.O.faces {f v}).image T.idO).min' h
  else ⟨0, hn⟩

/-- A colouring of a family `K` of simplices of a subdivision of `I` is **Sperner** w.r.t. `I`
(§2.2, printed p. 7, lines 286–288): the colours of each simplex `σ ∈ K` are among the original
colours of its carrier `carr_I(σ)`. -/
def IsSperner {n : ℕ} {VI VO : Type} (T : Task n VI VO) (K : Finset (Finset (VI → ℝ)))
    (col : (VI → ℝ) → Fin n) : Prop :=
  ∀ σ ∈ K, σ.image col ⊆ (carrOf T.I.faces (gs σ)).image T.idI

/-- A colouring is **proper** on a family of simplices: it is injective on every simplex. -/
def IsProper {E : Type} {n : ℕ} (K : Finset (Finset E)) (col : E → Fin n) : Prop :=
  ∀ σ ∈ K, Set.InjOn col (σ : Set E)

/-- The preimage subcomplex `pre^K_f(Σ) = {σ ∈ K : f(|σ|) ⊆ |Σ|}` (§4.2.1, printed p. 11). -/
noncomputable def pre {VI VO : Type} (K : Finset (Finset (VI → ℝ))) (f : (VI → ℝ) → (VO → ℝ))
    (S : Finset VO) : Finset (Finset (VI → ℝ)) :=
  K.filter fun σ => f '' gs σ ⊆ face S

/-- The colour `c_k` of an output simplex `Σ` with colours `c_0 < ⋯ < c_d` (printed p. 11,
line 438); `none` if `k > d`. -/
noncomputable def colorAt {n : ℕ} {VI VO : Type} (T : Task n VI VO) (S : Finset VO) (k : ℕ) :
    Option (Fin n) :=
  ((S.image T.idO).sort (· ≤ ·))[k]?

/-- **Definition 3** (printed p. 11): an edge `e = {v, v'}` is violated if
`col(v) = col(v')`. -/
def IsViolated {E : Type} {n : ℕ} (col : E → Fin n) (e : Finset E) : Prop :=
  e.card = 2 ∧ ∀ v ∈ e, ∀ w ∈ e, col v = col w

/-- **Definition 4** (printed p. 11): a simplex `σ` (of `pre^K_f(Σ)`) is shallow w.r.t. `col` if
`col(v) < c_{dim σ}` for every vertex `v ∈ σ`, where `c_0 < ⋯ < c_d` are the colours of `Σ`.
Guard: if `dim σ > dim Σ` (excluded by Lemma 6), `c_{dim σ}` does not exist and `σ` is not
shallow. Membership in `pre^K_f(Σ)` is stated separately where used. -/
def IsShallow {n : ℕ} {VI VO : Type} (T : Task n VI VO) (col : (VI → ℝ) → Fin n)
    (S : Finset VO) (σ : Finset (VI → ℝ)) : Prop :=
  σ.Nonempty ∧ ∃ c, colorAt T S (σ.card - 1) = some c ∧ ∀ v ∈ σ, col v < c

/-- **Definition 1** (stellar subdivision, printed p. 6): `ste(K, σ)` with new vertex `p`
(`p` a point of the interior of `|σ|`). Every simplex `γ ∈ K` with `σ ⊈ γ` is kept; every
`γ ∈ K` with `σ ⊆ γ` is replaced by the simplices `{p} ∪ (γ ∖ {u})`, `u ∈ σ`, and all their
nonempty faces. -/
noncomputable def stellar {E : Type} (K : Finset (Finset E)) (σ : Finset E) (p : E) :
    Finset (Finset E) :=
  K.filter (fun γ => ¬ σ ⊆ γ) ∪
    (K.filter (fun γ => σ ⊆ γ)).biUnion fun γ =>
      σ.biUnion fun u => (insert p (γ.erase u)).powerset.filter fun ρ => ρ.Nonempty

/-- The state of the refinement procedure: the current subdivision `K` (its simplices) and the
current colouring `col`. -/
abbrev RState (n : ℕ) (VI : Type) := Finset (Finset (VI → ℝ)) × ((VI → ℝ) → Fin n)

/-- One **push-down** step while handling `Σ` (printed p. 12, lines 462–465, 472–474): pick a
violated edge `e ∈ pre^K_f(Σ)` whose (common) colour is not `c_0`, stellarly subdivide `K` at `e`
with a new vertex `p` in the interior of `|e|`, and colour `p` with `c_0`. -/
def PushStep {n : ℕ} {VI VO : Type} (T : Task n VI VO) (f : (VI → ℝ) → (VO → ℝ))
    (S : Finset VO) (s s' : RState n VI) : Prop :=
  ∃ e c₀ p, e ∈ pre s.1 f S ∧ IsViolated s.2 e ∧ colorAt T S 0 = some c₀ ∧
    (∀ v ∈ e, s.2 v ≠ c₀) ∧ p ∈ openSimplex e ∧
    s' = (stellar s.1 e p, Function.update s.2 p c₀)

/-- The push-down loop has terminated: every violated edge of `pre^K_f(Σ)` is `c_0`-coloured. -/
def NoPush {n : ℕ} {VI VO : Type} (T : Task n VI VO) (f : (VI → ℝ) → (VO → ℝ))
    (S : Finset VO) (s : RState n VI) : Prop :=
  ∀ e ∈ pre s.1 f S, IsViolated s.2 e → ∀ c₀, colorAt T S 0 = some c₀ → ∀ v ∈ e, s.2 v = c₀

/-- One **shatter** step for `d'` while handling `Σ` (printed p. 12, lines 467–469, 479–480):
pick a shallow `d'`-simplex `σ ∈ pre^K_f(Σ)`, stellarly subdivide `K` at `σ` with a new vertex `p`
in the interior of `|σ|`, and colour `p` with `c_{d'}`. -/
def ShatterStep {n : ℕ} {VI VO : Type} (T : Task n VI VO) (f : (VI → ℝ) → (VO → ℝ))
    (S : Finset VO) (d' : ℕ) (s s' : RState n VI) : Prop :=
  ∃ σ c p, σ ∈ pre s.1 f S ∧ σ.card = d' + 1 ∧ IsShallow T s.2 S σ ∧
    colorAt T S d' = some c ∧ p ∈ openSimplex σ ∧
    s' = (stellar s.1 σ p, Function.update s.2 p c)

/-- The shatter loop for `d'` has terminated: `pre^K_f(Σ)` has no shallow `d'`-simplex. -/
def NoShallow {n : ℕ} {VI VO : Type} (T : Task n VI VO) (f : (VI → ℝ) → (VO → ℝ))
    (S : Finset VO) (d' : ℕ) (s : RState n VI) : Prop :=
  ∀ σ ∈ pre s.1 f S, σ.card = d' + 1 → ¬ IsShallow T s.2 S σ

/-- `ShatterLoops T f Σ k s s'`: the loops `for d' = k, k-1, …, 1` (each a `while` loop of shatter
steps run to termination) lead from `s` to `s'`. -/
def ShatterLoops {n : ℕ} {VI VO : Type} (T : Task n VI VO) (f : (VI → ℝ) → (VO → ℝ))
    (S : Finset VO) : ℕ → RState n VI → RState n VI → Prop
  | 0, s, s' => s' = s
  | k + 1, s, s' => ∃ s₁, Relation.ReflTransGen (ShatterStep T f S (k + 1)) s s₁ ∧
      NoShallow T f S (k + 1) s₁ ∧ ShatterLoops T f S k s₁ s'

/-- Handling the `d`-simplex `Σ` (`d = |Σ| - 1`) (printed p. 12, lines 461–469): push down
violated edges until none with colour `≠ c_0` is left, then for `d' = d, …, 1` shatter shallow
`d'`-simplices until none is left. Any legal choice of edge, simplex and interior point is
allowed. -/
def Phase {n : ℕ} {VI VO : Type} (T : Task n VI VO) (f : (VI → ℝ) → (VO → ℝ))
    (S : Finset VO) (s s' : RState n VI) : Prop :=
  ∃ s₁, Relation.ReflTransGen (PushStep T f S) s s₁ ∧ NoPush T f S s₁ ∧
    ShatterLoops T f S (S.card - 1) s₁ s'

/-- `ord = [Σ₁, …, Σ_m]` lists every simplex of `O` exactly once, in non-decreasing order of
dimension (printed p. 12, line 460). -/
def IsHandlingOrder {n : ℕ} {VI VO : Type} (T : Task n VI VO) (ord : List (Finset VO)) : Prop :=
  ord.Nodup ∧ (∀ S, S ∈ ord ↔ S ∈ T.O.faces) ∧ ord.Pairwise fun a b => a.card ≤ b.card

/-- A **completed run** of the refinement procedure (printed p. 12, lines 460–470) from the
subdivision `D = div(I)` with the colouring of Definition 2, handling `Σ₁, …, Σ_m = ord` in
order: `st 0 = (div(I), col)`, and `st t` is the state `(K_t, col_t)` after handling `Σ_t`
(`Σ_t = ord[t-1]`), for `1 ≤ t ≤ m`. The output is `div'(I) = K_m`, `col' = col_m`.
A vertex `v` is *created while handling* `Σ_s` when it is a vertex of `K_s` but not of
`K_{s-1}`. -/
def IsRun {n : ℕ} {VI VO : Type} (hn : 0 < n) (T : Task n VI VO) (f : (VI → ℝ) → (VO → ℝ))
    (D : GCx (VI → ℝ)) (ord : List (Finset VO)) (st : ℕ → RState n VI) : Prop :=
  st 0 = (D.faces, initColor hn T f) ∧
    ∀ (t : ℕ) (h : t < ord.length), Phase T f ord[t] (st t) (st (t + 1))

/-- A map on exactly the vertices of the current complex. In particular the empty
complex admits its empty vertex map even when `VO` is empty. -/
abbrev VertexMap {VI : Type} (K : Finset (Finset (VI → ℝ))) (VO : Type) :=
  {v : VI → ℝ // v ∈ verts K} → VO

/-- The face image of a map on the actual vertices. Used only for `σ ∈ K`; the filter
avoids imposing an artificial value for the map off its vertex domain. -/
noncomputable def vertexImage {VI VO : Type} (K : Finset (Finset (VI → ℝ)))
    (σ : Finset (VI → ℝ)) (φ : VertexMap K VO) : Finset VO :=
  ((verts K).attach.filter fun v => v.val ∈ σ).image φ

/-- **Definition 5** (printed p. 16), relational form: `φ` maps each actual vertex `v` of `K`
to a vertex of `carr_O(f(|v|))` whose colour is `col(v)`. These two requirements specify
exactly the source's choice, independently of simpliciality or carriedness. Lemma 13 asserts
existence and uniqueness of the choice, as well as the resulting map's properties. -/
def IsDecisionMap {n : ℕ} {VI VO : Type} (T : Task n VI VO) (f : (VI → ℝ) → (VO → ℝ))
    (K : Finset (Finset (VI → ℝ))) (col : (VI → ℝ) → Fin n) (φ : VertexMap K VO) : Prop :=
  ∀ v, φ v ∈ carrOf T.O.faces {f v.val} ∧ T.idO (φ v) = col v.val

end WaitFreeTasks.Characterization


