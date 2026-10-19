-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_Basic
-- name    : OAI_Probability_CriticalZ3_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:49:27.413596+00:00
-- url     : https://prove2.me/theorems/9bae2064-0253-47e3-9f1f-08af52ab51c7
-- title:
--   Measurability, trivial parameters and cube events for percolation on Z³
-- statement:
--   Vertices are points of $\mathbb Z^3$ and bonds are pairs $(x,i)$ joining $x$ to $x+e_i$, $i\in\{0,1,2\}$; a bond configuration assigns open/closed to bonds and a site configuration to vertices. Basic facts about bond and site percolation laws on $\mathbb Z^3$.
--
--   1. **Parameters and laws.** A real $p$ is clamped into $[0,1]$; the bond and site laws are probability measures, equal to the all-closed point mass at $p=0$ and the all-open point mass at $p=1$.
--   2. **Measurability.** Reachability along open bonds, or along open sites, is a countable union over path lengths, so connection events and the events $\{|\mathcal C(x)|=\infty\}$ are measurable.
--   3. **Extreme cases.** In the all-open configuration the ray $x,x+e_0,x+2e_0,\dots$ lies in the cluster of $x$, so clusters are infinite; in the all-closed configuration the bond cluster is $\{x\}$ and the site cluster is empty. Hence the infinite-cluster probability is $0$ at $p=0$ and $1$ at $p=1$.
--   4. **Cubes and seeds.** The cube is
--   $$
--   \Lambda_n(c)=\{x:\ |x_i-c_i|\le n\ \text{for all }i\},
--   $$
--   with boundary the points having some coordinate equal to $c_i\pm n$. The seed events say that some vertex of $\Lambda_m(c)$ has an infinite cluster, or reaches a target set $T$ by open paths staying in $\Lambda_n(c)$. The event that some cluster is infinite is also defined.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3

-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uOmega uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory
open _root_.MeasureTheory ProbabilityTheory

namespace CriticalZ3

@[simp] theorem parameter_coe {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (parameter p : ℝ) = p := by
  simp [parameter, min_eq_right hp.2, max_eq_right hp.1]

@[simp] theorem parameter_zero : parameter 0 = 0 := Subtype.ext (by simp [parameter])
@[simp] theorem parameter_one : parameter 1 = 1 := Subtype.ext (by simp [parameter])

instance bondLaw_probability (p : ℝ) : IsProbabilityMeasure (bondLaw p) := by
  unfold bondLaw
  infer_instance

instance siteLaw_probability (p : ℝ) : IsProbabilityMeasure (siteLaw p) := by
  unfold siteLaw
  infer_instance

@[simp] theorem bondLaw_zero : bondLaw 0 = Measure.dirac (fun _ => false) := by
  simp [bondLaw]

@[simp] theorem siteLaw_zero : siteLaw 0 = Measure.dirac (fun _ => false) := by
  simp [siteLaw]

@[simp] theorem bondLaw_one : bondLaw 1 = Measure.dirac (fun _ => true) := by
  simp [bondLaw]

@[simp] theorem siteLaw_one : siteLaw 1 = Measure.dirac (fun _ => true) := by
  simp [siteLaw]

/-- Finite path length, used solely to prove measurability of reachability. -/
def PathLength {V : Type uV} (r : V → V → Prop) : ℕ → V → V → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, PathLength r n x z ∧ r z y

theorem pathLength_rtg {V : Type uV} {r : V → V → Prop} {n : ℕ} {x y : V}
    (h : PathLength r n x y) : Relation.ReflTransGen r x y := by
  induction n generalizing y with
  | zero => cases h; exact .refl
  | succ n ih =>
    obtain ⟨z, hz, hy⟩ := h
    exact (ih hz).tail hy

theorem rtg_iff_exists_pathLength {V : Type uV} {r : V → V → Prop} {x y : V} :
    Relation.ReflTransGen r x y ↔ ∃ n, PathLength r n x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail y z _ hy ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, y, hn, hy⟩
  · rintro ⟨n, hn⟩
    exact pathLength_rtg hn

theorem measurableSet_rtg {Ω : Type uOmega} {V : Type uV} [MeasurableSpace Ω] [Countable V]
    (r : Ω → V → V → Prop) (hr : ∀ x y, MeasurableSet {ω | r ω x y}) (x y : V) :
    MeasurableSet {ω | Relation.ReflTransGen (r ω) x y} := by
  have hpath (n : ℕ) (x y : V) : MeasurableSet {ω | PathLength (r ω) n x y} := by
    induction n generalizing x y with
    | zero => simp only [PathLength]; exact MeasurableSet.const _
    | succ n ih =>
      simp only [PathLength, Set.ofPred_exists]
      exact MeasurableSet.iUnion (fun z => (ih x z).inter (hr z y))
  simp only [rtg_iff_exists_pathLength, Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n => hpath n x y)

theorem measurableSet_bondOpen (x y : Vertex) :
    MeasurableSet {ω : BondConfig | BondOpen ω x y} := by
  unfold BondOpen
  simp only [Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion (fun i => (MeasurableSet.const _).inter
      (measurableSet_eq_fun (measurable_pi_apply (x, i)) measurable_const))
  · exact MeasurableSet.iUnion (fun i => (MeasurableSet.const _).inter
      (measurableSet_eq_fun (measurable_pi_apply (y, i)) measurable_const))

theorem measurableSet_siteOpen (x y : Vertex) :
    MeasurableSet {ω : SiteConfig | SiteOpen ω x y} := by
  exact (MeasurableSet.const _).inter
    ((measurableSet_eq_fun (measurable_pi_apply x) measurable_const).inter
      (measurableSet_eq_fun (measurable_pi_apply y) measurable_const))

theorem measurableSet_bondConnected (x y : Vertex) :
    MeasurableSet {ω : BondConfig | BondConnected ω x y} :=
  measurableSet_rtg BondOpen measurableSet_bondOpen x y

theorem measurableSet_siteConnected (x y : Vertex) :
    MeasurableSet {ω : SiteConfig | SiteConnected ω x y} :=
  (measurableSet_eq_fun (measurable_pi_apply x) measurable_const).inter
    (measurableSet_rtg SiteOpen measurableSet_siteOpen x y)

theorem infinite_iff_escape_finset {V : Type uV} (s : Set V) :
    s.Infinite ↔ ∀ t : Finset V, ∃ y ∈ s, y ∉ t := by
  classical
  constructor
  · exact fun hs t => hs.exists_notMem_finset t
  · intro h hs
    obtain ⟨y, hy, hn⟩ := h hs.toFinset
    exact hn (hs.mem_toFinset.mpr hy)

theorem measurableSet_infinite_fiber {Ω : Type uOmega} {V : Type uV} [MeasurableSpace Ω] [Countable V]
    (r : Ω → V → Prop) (hr : ∀ y, MeasurableSet {ω | r ω y}) :
    MeasurableSet {ω | {y | r ω y}.Infinite} := by
  simp only [infinite_iff_escape_finset, Set.mem_ofPred_eq]
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro t
  rw [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun y => (hr y).inter (MeasurableSet.const _))

theorem measurableSet_bondInfiniteAt (x : Vertex) : MeasurableSet (bondInfiniteAt x) :=
  measurableSet_infinite_fiber (fun ω y => BondConnected ω x y)
    (measurableSet_bondConnected x)

theorem measurableSet_siteInfiniteAt (x : Vertex) : MeasurableSet (siteInfiniteAt x) :=
  measurableSet_infinite_fiber (fun ω y => SiteConnected ω x y)
    (measurableSet_siteConnected x)

/-- An infinite nearest-neighbor ray, used to certify supercriticality at one. -/
def ray (x : Vertex) (n : ℕ) : Vertex :=
  fun j => x j + if j = 0 then (n : ℤ) else 0

@[simp] theorem ray_zero (x : Vertex) : ray x 0 = x := by
  ext j
  simp [ray]

@[simp] theorem ray_succ (x : Vertex) (n : ℕ) : ray x (n + 1) = step (ray x n) 0 := by
  ext j
  by_cases hj : j = 0
  · subst j; simp [ray, step]; omega
  · simp [ray, step, hj, Ne.symm hj]

theorem ray_injective (x : Vertex) : Function.Injective (ray x) := by
  intro n m h
  have he := congrFun h 0
  simp only [ray] at he
  exact Int.ofNat_inj.mp (add_left_cancel he)

theorem bondConnected_open_ray (x : Vertex) (n : ℕ) :
    BondConnected (fun _ => true) x (ray x n) := by
  induction n with
  | zero => rw [ray_zero]; exact .refl
  | succ n ih =>
    apply ih.tail
    exact Or.inl ⟨0, ray_succ x n, rfl⟩

theorem siteConnected_open_ray (x : Vertex) (n : ℕ) :
    SiteConnected (fun _ => true) x (ray x n) := by
  refine ⟨rfl, ?_⟩
  induction n with
  | zero => rw [ray_zero]
  | succ n ih =>
    apply ih.tail
    exact ⟨⟨0, Or.inl (ray_succ x n)⟩, rfl, rfl⟩

theorem bondCluster_open_infinite (x : Vertex) : (bondCluster (fun _ => true) x).Infinite :=
  (Set.infinite_range_of_injective (ray_injective x)).mono
    (by rintro y ⟨n, rfl⟩; exact bondConnected_open_ray x n)

theorem siteCluster_open_infinite (x : Vertex) : (siteCluster (fun _ => true) x).Infinite :=
  (Set.infinite_range_of_injective (ray_injective x)).mono
    (by rintro y ⟨n, rfl⟩; exact siteConnected_open_ray x n)

@[simp] theorem bondCluster_closed (x : Vertex) : bondCluster (fun _ => false) x = {x} := by
  ext y
  change Relation.ReflTransGen (BondOpen (fun _ => false)) x y ↔ y = x
  apply Relation.reflTransGen_iff_eq
  intro y h
  rcases h with ⟨i, _, hi⟩ | ⟨i, _, hi⟩ <;> cases hi

@[simp] theorem siteCluster_closed (x : Vertex) : siteCluster (fun _ => false) x = ∅ := by
  ext y
  simp [siteCluster, SiteConnected]

@[simp] theorem bondLaw_zero_infinite (x : Vertex) : bondLaw 0 (bondInfiniteAt x) = 0 := by
  rw [bondLaw_zero, Measure.dirac_apply' _ (measurableSet_bondInfiniteAt x)]
  simp [bondInfiniteAt]

@[simp] theorem siteLaw_zero_infinite (x : Vertex) : siteLaw 0 (siteInfiniteAt x) = 0 := by
  rw [siteLaw_zero, Measure.dirac_apply' _ (measurableSet_siteInfiniteAt x)]
  simp [siteInfiniteAt]

@[simp] theorem bondLaw_one_infinite (x : Vertex) : bondLaw 1 (bondInfiniteAt x) = 1 := by
  rw [bondLaw_one, Measure.dirac_apply' _ (measurableSet_bondInfiniteAt x)]
  simp [bondInfiniteAt, bondCluster_open_infinite]

@[simp] theorem siteLaw_one_infinite (x : Vertex) : siteLaw 1 (siteInfiniteAt x) = 1 := by
  rw [siteLaw_one, Measure.dirac_apply' _ (measurableSet_siteInfiniteAt x)]
  simp [siteInfiniteAt, siteCluster_open_infinite]

/-! Finite alterations, tail invariance, and the infinite seed limit. -/

/-- A negative coordinate step, needed only to list all finitely many neighbors. -/
def backstep (x : Vertex) (i : Fin 3) : Vertex := fun j => x j - if i = j then 1 else 0

@[simp] theorem step_backstep (x : Vertex) (i : Fin 3) : step (backstep x i) i = x := by
  funext j
  simp [step, backstep]

@[simp] theorem backstep_step (x : Vertex) (i : Fin 3) : backstep (step x i) i = x := by
  funext j
  simp [step, backstep]

def bondExistsInfinite : Set BondConfig := {ω | ∃ x, (bondCluster ω x).Infinite}
def siteExistsInfinite : Set SiteConfig := {ω | ∃ x, (siteCluster ω x).Infinite}

open Filter
open scoped Topology

def cube (c : Vertex) (n : ℕ) : Set Vertex :=
  Set.Icc (fun i => c i - (n : ℤ)) (fun i => c i + (n : ℤ))

theorem mem_cube {c x : Vertex} {n : ℕ} :
    x ∈ cube c n ↔ ∀ i, c i - (n : ℤ) ≤ x i ∧ x i ≤ c i + (n : ℤ) := by
  simp only [cube,Set.mem_Icc,Pi.le_def,forall_and]

theorem cube_finite (c : Vertex) (n : ℕ) : (cube c n).Finite := Set.finite_Icc _ _

theorem exists_mem_cube (c x : Vertex) : ∃ n, x ∈ cube c n := by
  let n := Finset.univ.sup (fun i : Fin 3 => (x i - c i).natAbs)
  refine ⟨n,mem_cube.mpr (fun i => ?_)⟩
  have hn : ((x i - c i).natAbs : ℤ) ≤ n := by
    exact_mod_cast (Finset.le_sup (f := fun i : Fin 3 => (x i - c i).natAbs) (Finset.mem_univ i))
  have hu := Int.le_natAbs (a := x i - c i)
  have hl := Int.le_natAbs (a := -(x i - c i))
  simp only [Int.natAbs_neg] at hl
  constructor <;> omega

@[simp] theorem iUnion_cube (c : Vertex) : (⋃ n, cube c n) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
  exact exists_mem_cube c x

def bondSeedInfinite (c : Vertex) (n : ℕ) : Set BondConfig :=
  {ω | ∃ x ∈ cube c n, ω ∈ bondInfiniteAt x}
def siteSeedInfinite (c : Vertex) (n : ℕ) : Set SiteConfig :=
  {ω | ∃ x ∈ cube c n, ω ∈ siteInfiniteAt x}

/-- The closed-cube vertex boundary used by the finite-scale argument. -/
def cubeBoundary (c : Vertex) (n : ℕ) : Set Vertex :=
  {x | x ∈ cube c n ∧ ∃ i, x i = c i - (n : ℤ) ∨ x i = c i + (n : ℤ)}

def Within {V : Type uV} (D : Set V) (r : V → V → Prop) (x y : V) : Prop :=
  x ∈ D ∧ y ∈ D ∧ r x y

def bondSeedReaches (c : Vertex) (m n : ℕ) (T : Set Vertex) : Set BondConfig :=
  {ω | ∃ x ∈ cube c m, ∃ y ∈ T,
    Relation.ReflTransGen (Within (cube c n) (BondOpen ω)) x y}
def siteSeedReaches (c : Vertex) (m n : ℕ) (T : Set Vertex) : Set SiteConfig :=
  {ω | ∃ x ∈ cube c m, ω x = true ∧ ∃ y ∈ T,
    Relation.ReflTransGen (Within (cube c n) (SiteOpen ω)) x y}

end CriticalZ3

end OAI


