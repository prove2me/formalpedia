-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Trace
-- name    : BCFGJPSSV26_Greedy_Trace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:51.027334+00:00
-- url     : https://prove2.me/theorems/21880f1f-b0ab-4197-a603-ebd4e100795a
-- title:
--   BCFGJPSSV26.Greedy.Trace — The execution of a solution
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Trace` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26a, Appendix E.1]: the execution of an `η`-valid solution `H` opens the atoms of
--   `H₀, H₁, …` in order and raises the time after each sequence of type 2. Its **atomic steps**
--   (`BCFGJPSSV26.Greedy.Run.steps`) are the openings and the raises; step `s` sees the atoms `pre s`
--   opened before it and the profile `Dpre s`.
--
--   Everything is indexed by steps, which replaces the paper's three indexings (clients `k`, open sets
--   `S_k`, and `s(j)`):
--
--   * `σ j` (`BCFGJPSSV26.Greedy.Run.σ`): the step after which client `j` is first inactive;
--   * `wit s` (`BCFGJPSSV26.Greedy.Run.wit`): for a regular opening of type 2, the superset `S̃` and
--     the parameter `T` of the bids it was opened with (the prefix itself whenever possible); for
--     every other step, the prefix and `θ`;
--   * `αs j` (`BCFGJPSSV26.Greedy.Run.αs`): the paper's `α*_j`;
--   * `Xv j s` (`BCFGJPSSV26.Greedy.Run.Xv`): the paper's `R_{j,·}` at step `s ≥ σ j`: `α*_j` at
--     `s = σ j`, then `(1 - δ) d(j, S)`;
--   * `Zv j s` (`BCFGJPSSV26.Greedy.Run.Zv`): the paper's `Z_{j,·}` and `ζ_{j,·}`;
--   * `contrib j s` (`BCFGJPSSV26.Greedy.Run.contrib`): what client `j` pays towards the facility
--     opened at step `s`;
--   * `key j` (`BCFGJPSSV26.Greedy.Run.key`): the order of the clients, by `(σ j, α*_j, j)`.
--
--   The observations of the paper ([BCFGJPSSV26a, Observations E.2, E.3 and E.4]) and the bounds on
--   the contributions are `BCFGJPSSV26.Greedy.Run.Xv_anti`, `BCFGJPSSV26.Greedy.Run.obs_tau`,
--   `BCFGJPSSV26.Greedy.Run.Zv_le_Xv`, `BCFGJPSSV26.Greedy.Run.contrib_le`; the freezing lemma
--   ([BCFGJPSSV26a, Lemma E.8]) and [BCFGJPSSV26a, Lemma E.11] are `BCFGJPSSV26.Greedy.Run.freezing`
--   and `BCFGJPSSV26.Greedy.Run.superset_far`.
--
--   The steps are built block by block (`BCFGJPSSV26.Greedy.Run.block`: the atoms of `H_p`, then a
--   raise if `p` is odd). `BCFGJPSSV26.Greedy.Run.step_spec` describes step `s` through its block: the
--   prefix `pre s` is `H_0 ++ … ++ H_{p-1}` followed by the first `t` atoms of `H_p`, and the atom it
--   opens, if any, is `H_p[t]`; the time of a step is `θ` of the number of raises before it
--   (`BCFGJPSSV26.Greedy.Run.θs_eq`).
--
--   **Contents.** The module is published as a whole: 131 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.Run.noOver_post`, `BCFGJPSSV26.Greedy.Run.noOver_pre`, `BCFGJPSSV26.Greedy.Run.superset_far` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Trace`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Trace.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Structure
public import Mathlib.Data.Prod.Lex

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Trace` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The execution of a solution

[BCFGJPSSV26a, Appendix E.1]: the execution of an `η`-valid solution `H` opens the atoms of
`H₀, H₁, …` in order and raises the time after each sequence of type 2. Its **atomic steps**
(`BCFGJPSSV26.Greedy.Run.steps`) are the openings and the raises; step `s` sees the atoms `pre s`
opened before it and the profile `Dpre s`.

Everything is indexed by steps, which replaces the paper's three indexings (clients `k`, open sets
`S_k`, and `s(j)`):

* `σ j` (`BCFGJPSSV26.Greedy.Run.σ`): the step after which client `j` is first inactive;
* `wit s` (`BCFGJPSSV26.Greedy.Run.wit`): for a regular opening of type 2, the superset `S̃` and
  the parameter `T` of the bids it was opened with (the prefix itself whenever possible); for
  every other step, the prefix and `θ`;
* `αs j` (`BCFGJPSSV26.Greedy.Run.αs`): the paper's `α*_j`;
* `Xv j s` (`BCFGJPSSV26.Greedy.Run.Xv`): the paper's `R_{j,·}` at step `s ≥ σ j`: `α*_j` at
  `s = σ j`, then `(1 - δ) d(j, S)`;
* `Zv j s` (`BCFGJPSSV26.Greedy.Run.Zv`): the paper's `Z_{j,·}` and `ζ_{j,·}`;
* `contrib j s` (`BCFGJPSSV26.Greedy.Run.contrib`): what client `j` pays towards the facility
  opened at step `s`;
* `key j` (`BCFGJPSSV26.Greedy.Run.key`): the order of the clients, by `(σ j, α*_j, j)`.

The observations of the paper ([BCFGJPSSV26a, Observations E.2, E.3 and E.4]) and the bounds on
the contributions are `BCFGJPSSV26.Greedy.Run.Xv_anti`, `BCFGJPSSV26.Greedy.Run.obs_tau`,
`BCFGJPSSV26.Greedy.Run.Zv_le_Xv`, `BCFGJPSSV26.Greedy.Run.contrib_le`; the freezing lemma
([BCFGJPSSV26a, Lemma E.8]) and [BCFGJPSSV26a, Lemma E.11] are `BCFGJPSSV26.Greedy.Run.freezing`
and `BCFGJPSSV26.Greedy.Run.superset_far`.

The steps are built block by block (`BCFGJPSSV26.Greedy.Run.block`: the atoms of `H_p`, then a
raise if `p` is odd). `BCFGJPSSV26.Greedy.Run.step_spec` describes step `s` through its block: the
prefix `pre s` is `H_0 ++ … ++ H_{p-1}` followed by the first `t` atoms of `H_p`, and the atom it
opens, if any, is `H_p[t]`; the time of a step is `θ` of the number of raises before it
(`BCFGJPSSV26.Greedy.Run.θs_eq`).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

/-- A **run**: a space, parameters, an opening cost and an `η`-valid solution, with the
hypotheses of the analysis. -/
structure Run (n m : ℕ) where
  /-- The space. -/
  X : Space n m
  /-- The parameters. -/
  P : Par
  /-- The opening cost `f̂`. -/
  f : ℚ
  /-- The solution. -/
  H : List (List (Atom m))
  good : P.Good n
  d1 : ∀ j i, 1 ≤ X.d j i
  fpos : n * P.η < f
  sol : Sol P X.d f P.η H

/-- The kind of an atomic step: an opening or a raise of the time. -/
inductive Kind (m : ℕ) where
  | op (a : Atom m)
  | raise

/-- The atom opened by a step, if any. -/
def Kind.atom? {m : ℕ} : Kind m → Option (Atom m)
  | .op a => some a
  | .raise => none

/-- Whether a step raises the time. -/
def Kind.isRaise {m : ℕ} : Kind m → Bool
  | .op _ => false
  | .raise => true

/-- An atomic step of sequence `seq`. -/
structure Step (m : ℕ) where
  /-- The sequence of the step. -/
  seq : ℕ
  /-- The kind of the step. -/
  kind : Kind m

namespace Run

variable {n m : ℕ} (R : Run n m)

/-! ### Steps -/

/-- The atomic steps: the atoms of each sequence in order, followed by a raise after each
sequence of type 2. -/
def steps : List (Step m) := (List.range (2 * R.P.R)).flatMap fun p ↦
  ((R.H.getD p []).map fun a ↦ ⟨p, .op a⟩) ++ (if p % 2 = 1 then [⟨p, .raise⟩] else [])

/-- The number of steps. -/
def len : ℕ := R.steps.length

/-- Step `s`. -/
def step (s : ℕ) : Step m := R.steps.getD s ⟨0, .raise⟩

/-- The atoms opened before step `s`. -/
def pre (s : ℕ) : List (Atom m) := (R.steps.take s).filterMap fun t ↦ t.kind.atom?

/-- The profile before step `s`. -/
def Dpre (s : ℕ) : Fin n → ℚ := profL R.P.K R.X.d (R.pre s)

/-- The time of step `s`. -/
def θs (s : ℕ) : ℚ := R.P.θseq (R.step s).seq

/-- The time after step `s`. -/
def θpost (s : ℕ) : ℚ := if (R.step s).kind.isRaise then R.P.θplus (R.θs s) else R.θs s

/-- Client `j` is inactive after step `s`. -/
def Inact (s : ℕ) (j : Fin n) : Prop := (1 - R.P.δ) * R.Dpre (s + 1) j ≤ R.θpost s

open Classical in
/-- The step after which client `j` is first inactive (`len` if there is none, which does not
happen). -/
noncomputable def σ (j : Fin n) : ℕ :=
  if h : ∃ s, s < R.len ∧ R.Inact s j then Nat.find h else R.len

/-- Step `s` opens the regular atom `a` in a sequence of type 2. -/
def IsOp2 (s : ℕ) (a : Atom m) : Prop :=
  (R.step s).kind = .op a ∧ typ1 (R.step s).seq = false ∧ a.free = false

/-- Step `s` opens a regular atom. -/
def IsReg (s : ℕ) : Prop := ∃ a, (R.step s).kind = .op a ∧ a.free = false

/-- The witness `(S̃, T)` of the opening of `a` at step `s`: a superset of the prefix with
nonnegative offsets and a parameter `T ∈ [θ, (1 + ε²) θ]` for which (iii) and (iv) hold. -/
def WitOK (s : ℕ) (a : Atom m) (S : Finset (Fin m × ℚ)) (T : ℚ) : Prop :=
  pairs (R.pre s) ⊆ S ∧ (∀ q ∈ S, 0 ≤ q.2) ∧ R.θs s ≤ T ∧ T ≤ R.P.θplus (R.θs s) ∧
    R.f - n * R.P.η ≤ lhs3 R.P R.X.d (R.θs s) (profF R.P.K R.X.d S) a.fac T ∧
    ∀ i₀, lhs4 R.P R.X.d (R.θs s) (profF R.P.K R.X.d S) a.fac T i₀ ≤ R.f

open Classical in
/-- The witness of step `s`: for a regular opening of type 2, the prefix itself if possible,
otherwise some superset, with a parameter `T`; for every other step, the prefix and `θ`. -/
noncomputable def wit (s : ℕ) : Finset (Fin m × ℚ) × ℚ :=
  match (R.step s).kind with
  | .op a =>
    if typ1 (R.step s).seq = false ∧ a.free = false then
      if h : ∃ T, R.WitOK s a (pairs (R.pre s)) T then (pairs (R.pre s), h.choose)
      else if h' : ∃ S T, R.WitOK s a S T then (h'.choose, h'.choose_spec.choose)
      else (pairs (R.pre s), R.θs s)
    else (pairs (R.pre s), R.θs s)
  | .raise => (pairs (R.pre s), R.θs s)

/-- The profile of the witness of step `s`. -/
noncomputable def Dt (s : ℕ) : Fin n → ℚ := profF R.P.K R.X.d (R.wit s).1

/-- The parameter of the witness of step `s`. -/
noncomputable def Tt (s : ℕ) : ℚ := (R.wit s).2

/-- The paper's **`α*_j`**: the value of client `j` when it becomes inactive. -/
noncomputable def αs (j : Fin n) : ℚ :=
  match (R.step (R.σ j)).kind with
  | .raise => (1 - R.P.δ) * R.Dpre (R.σ j) j
  | .op a =>
    if typ1 (R.step (R.σ j)).seq = true ∨ a.free = true then R.θs (R.σ j)
    else if R.θs (R.σ j) < (1 - R.P.δ) * R.Dt (R.σ j) j then
      mT R.P R.X.d (R.θs (R.σ j)) (R.Dt (R.σ j)) a.fac (R.Tt (R.σ j)) j
    else R.θs (R.σ j)

/-- The paper's `R_{j,·}` at step `s ≥ σ j`: `α*_j` at `σ j`, then `(1 - δ) d(j, S)`. -/
noncomputable def Xv (j : Fin n) (s : ℕ) : ℚ :=
  if s = R.σ j then R.αs j else (1 - R.P.δ) * R.Dpre s j

/-- The paper's `Z_{j,·}` (and `ζ_{j,·}`) at step `s`. -/
noncomputable def Zv (j : Fin n) (s : ℕ) : ℚ :=
  if R.θs s < (1 - R.P.δ) * R.Dt s j then (if R.σ j = s then R.αs j else R.θs s)
  else (1 - R.P.δ) * R.Dt s j

/-- What client `j` pays towards the regular facility opened at step `s`. -/
noncomputable def contrib (j : Fin n) (s : ℕ) : ℚ :=
  match (R.step s).kind with
  | .op a =>
    if a.free = true then 0
    else if typ1 (R.step s).seq = true then
      bid (mval R.P (R.θs s) (R.Dt s) j) ((1 - R.P.δ) * R.X.d j a.fac)
    else bid (mT R.P R.X.d (R.θs s) (R.Dt s) a.fac (R.Tt s) j) ((1 - R.P.δ / 2) * R.X.d j a.fac)
  | .raise => 0

/-- The order of the clients: by the step at which they become inactive, then by `α*`, then by
index. -/
noncomputable def key (j : Fin n) : Lex (ℕ × Lex (ℚ × ℕ)) := toLex (R.σ j, toLex (R.αs j, j.val))

theorem key_injective : Function.Injective R.key := by
  intro j j' h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  exact Fin.ext h.2.2

/-! ### Blocks of steps -/

/-- The steps of sequence `p`: its atoms, followed by a raise if `p` is odd. -/
def block (p : ℕ) : List (Step m) :=
  ((R.H.getD p []).map fun a ↦ ⟨p, .op a⟩) ++ (if p % 2 = 1 then [⟨p, .raise⟩] else [])

/-- The steps of the first `q` sequences. -/
def stepsTo (q : ℕ) : List (Step m) := (List.range q).flatMap R.block

/-- The number of raises in a list of steps. -/
def nRaise (l : List (Step m)) : ℕ := l.countP fun t ↦ t.kind.isRaise

/-- The atoms opened in a list of steps. -/
def atoms (l : List (Step m)) : List (Atom m) := l.filterMap fun t ↦ t.kind.atom?

theorem steps_eq : R.steps = R.stepsTo (2 * R.P.R) := rfl

theorem pre_eq (s : ℕ) : R.pre s = atoms (R.steps.take s) := rfl

theorem stepsTo_succ (q : ℕ) : R.stepsTo (q + 1) = R.stepsTo q ++ R.block q := by
  simp [stepsTo, List.range_succ, List.flatMap_append]

theorem length_block (p : ℕ) :
    (R.block p).length = (R.H.getD p []).length + (if p % 2 = 1 then 1 else 0) := by
  unfold block
  split_ifs <;> simp

theorem seq_of_mem_block {p : ℕ} {x : Step m} (hx : x ∈ R.block p) : x.seq = p := by
  unfold block at hx
  split_ifs at hx <;> simp at hx <;> aesop

theorem atoms_append (l l' : List (Step m)) : atoms (l ++ l') = atoms l ++ atoms l' :=
  List.filterMap_append

theorem nRaise_append (l l' : List (Step m)) : nRaise (l ++ l') = nRaise l + nRaise l' :=
  List.countP_append

theorem atoms_map_op (p : ℕ) (L : List (Atom m)) :
    atoms (L.map fun a ↦ (⟨p, .op a⟩ : Step m)) = L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, atoms, List.filterMap_cons, Kind.atom?] at ih ⊢
    rw [ih]

theorem nRaise_map_op (p : ℕ) (L : List (Atom m)) :
    nRaise (L.map fun a ↦ (⟨p, .op a⟩ : Step m)) = 0 := by
  simp [nRaise, List.countP_map, Function.comp_def, Kind.isRaise]

theorem atoms_take_raise (p t : ℕ) :
    atoms ((if p % 2 = 1 then [(⟨p, .raise⟩ : Step m)] else []).take t) = [] := by
  split_ifs
  · cases t <;> simp [atoms, Kind.atom?]
  · simp [atoms]

theorem atoms_block_take (p t : ℕ) :
    atoms ((R.block p).take t) = (R.H.getD p []).take t := by
  unfold block
  rw [List.take_append, atoms_append, atoms_take_raise, List.append_nil, ← List.map_take,
    atoms_map_op]

theorem atoms_block (p : ℕ) : atoms (R.block p) = R.H.getD p [] := by
  have h := R.atoms_block_take p (R.block p).length
  rwa [List.take_length, List.take_of_length_le (by rw [length_block]; omega)] at h

theorem nRaise_block_take {p t : ℕ} (ht : t < (R.block p).length) :
    nRaise ((R.block p).take t) = 0 := by
  have ht' : t ≤ (R.H.getD p []).length := by rw [length_block] at ht; split_ifs at ht <;> omega
  unfold block
  rw [List.take_append_of_le_length (by simpa using ht'), ← List.map_take, nRaise_map_op]

theorem nRaise_block (p : ℕ) : nRaise (R.block p) = if p % 2 = 1 then 1 else 0 := by
  unfold block
  rw [nRaise_append, nRaise_map_op]
  split_ifs <;> simp [nRaise, Kind.isRaise]

theorem nRaise_stepsTo (q : ℕ) : nRaise (R.stepsTo q) = q / 2 := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [stepsTo_succ, nRaise_append, ih, nRaise_block]
    split_ifs <;> omega

theorem flatten_take_succ (H : List (List (Atom m))) (q : ℕ) :
    (H.take (q + 1)).flatten = (H.take q).flatten ++ H.getD q [] := by
  rw [List.take_add_one, List.flatten_append]
  rcases Nat.lt_or_ge q H.length with h | h
  · simp [List.getElem?_eq_getElem h]
  · simp [List.getElem?_eq_none h]

theorem atoms_stepsTo (q : ℕ) : atoms (R.stepsTo q) = (R.H.take q).flatten := by
  induction q with
  | zero => rfl
  | succ q ih => rw [stepsTo_succ, atoms_append, ih, atoms_block, flatten_take_succ]

/-- Step `s` of the first `q` sequences is step `t` of some block `p < q`. -/
theorem exists_block_aux (q s : ℕ) (hs : s < (R.stepsTo q).length) :
    ∃ p < q, ∃ t < (R.block p).length,
      (R.stepsTo q).take s = R.stepsTo p ++ (R.block p).take t ∧
        (R.stepsTo q)[s]? = (R.block p)[t]? := by
  induction q with
  | zero => simp [stepsTo] at hs
  | succ q ih =>
    rw [stepsTo_succ] at hs ⊢
    by_cases h : s < (R.stepsTo q).length
    · obtain ⟨p, hp, t, ht, h1, h2⟩ := ih h
      refine ⟨p, by omega, t, ht, ?_, ?_⟩
      · rw [List.take_append_of_le_length h.le, h1]
      · rw [List.getElem?_append_left h, h2]
    · push Not at h
      rw [List.length_append] at hs
      refine ⟨q, by omega, s - (R.stepsTo q).length, by omega, ?_, ?_⟩
      · rw [List.take_append, List.take_of_length_le h]
      · rw [List.getElem?_append_right h]

theorem getElem?_block_lt {p t : ℕ} (ht : t < (R.H.getD p []).length) :
    (R.block p)[t]? = some ⟨p, .op (R.H.getD p [])[t]⟩ := by
  unfold block
  rw [List.getElem?_append_left (by simpa using ht), List.getElem?_map,
    List.getElem?_eq_getElem ht]
  rfl

theorem getElem?_block_ge {p t : ℕ} (ht : (R.H.getD p []).length ≤ t) {x : Step m}
    (hx : (R.block p)[t]? = some x) : x.kind = .raise := by
  unfold block at hx
  rw [List.getElem?_append_right (by simpa using ht)] at hx
  split_ifs at hx
  · have := List.mem_of_getElem? hx
    simp only [List.mem_singleton] at this
    rw [this]
  · simp at hx

/-- Step `s` is step `t` of the block of some sequence `p < 2R`. -/
theorem exists_block {s : ℕ} (hs : s < R.len) :
    ∃ p < 2 * R.P.R, ∃ t < (R.block p).length,
      R.steps.take s = R.stepsTo p ++ (R.block p).take t ∧
        (R.block p)[t]? = some (R.step s) := by
  obtain ⟨p, hp, t, ht, h1, h2⟩ := R.exists_block_aux _ s hs
  refine ⟨p, hp, t, ht, h1, ?_⟩
  unfold step
  rw [List.getD_eq_getElem?_getD, steps_eq, h2, List.getElem?_eq_getElem ht, Option.getD_some]

theorem steps_getElem? {s : ℕ} (hs : s < R.len) : R.steps[s]? = some (R.step s) := by
  unfold step
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, Option.getD_some]

/-- **The shape of step `s`**: it is in sequence `p < 2R` after `t` atoms of `H_p`, `p / 2`
raises precede it, and if it opens an atom, the atom is `H_p[t]`. -/
theorem step_spec {s : ℕ} (hs : s < R.len) :
    (R.step s).seq < 2 * R.P.R ∧ ∃ t ≤ (R.H.getD (R.step s).seq []).length,
      R.pre s = (R.H.take (R.step s).seq).flatten ++ (R.H.getD (R.step s).seq []).take t ∧
      nRaise (R.steps.take s) = (R.step s).seq / 2 ∧
      ∀ a, (R.step s).kind = .op a → ∃ ht : t < (R.H.getD (R.step s).seq []).length,
        (R.H.getD (R.step s).seq [])[t] = a := by
  obtain ⟨p, hp, t, ht, h1, h2⟩ := R.exists_block hs
  have hseq : (R.step s).seq = p := R.seq_of_mem_block (List.mem_of_getElem? h2)
  rw [hseq]
  have ht' : t ≤ (R.H.getD p []).length := by rw [length_block] at ht; split_ifs at ht <;> omega
  refine ⟨hp, t, ht', ?_, ?_, ?_⟩
  · rw [pre_eq, h1, atoms_append, atoms_stepsTo, atoms_block_take]
  · rw [h1, nRaise_append, nRaise_stepsTo, R.nRaise_block_take ht, add_zero]
  · intro a ha
    rcases Nat.lt_or_ge t (R.H.getD p []).length with hlt | hge
    · refine ⟨hlt, ?_⟩
      rw [R.getElem?_block_lt hlt, Option.some_inj] at h2
      rw [← h2] at ha
      exact Kind.op.inj ha
    · rw [R.getElem?_block_ge hge h2] at ha
      exact absurd ha (by simp)

theorem nRaise_take_succ {s : ℕ} (hs : s < R.len) :
    nRaise (R.steps.take (s + 1)) =
      nRaise (R.steps.take s) + (if (R.step s).kind.isRaise then 1 else 0) := by
  rw [List.take_add_one, nRaise_append, R.steps_getElem? hs]
  simp [nRaise, List.countP_cons]

theorem θs_eq {s : ℕ} (hs : s < R.len) : R.θs s = R.P.θ (nRaise (R.steps.take s)) := by
  rw [θs, Par.θseq, (R.step_spec hs).2.choose_spec.2.2.1]

theorem θpost_eq_θ {s : ℕ} (hs : s < R.len) :
    R.θpost s = R.P.θ (nRaise (R.steps.take (s + 1))) := by
  rw [R.nRaise_take_succ hs, θpost, R.θs_eq hs]
  split_ifs with h
  · rw [Par.θ_succ, Par.θplus]
  · rw [add_zero]

theorem nRaise_steps : nRaise R.steps = R.P.R := by
  rw [steps_eq, nRaise_stepsTo]
  omega

theorem pre_len' : R.pre R.len = R.H.flatten := by
  rw [pre_eq, len, List.take_length, steps_eq, atoms_stepsTo,
    List.take_of_length_le R.sol.1.le]

/-! ### Steps and times -/

theorem f_nonneg : 0 ≤ R.f := by
  have := R.fpos
  have := R.good.η_nonneg
  have : (0 : ℚ) ≤ n * R.P.η := by positivity
  linarith

theorem K_pos : 0 < R.P.K := by
  have := R.good.K_ge
  have := R.P.one_le_θ R.P.R
  linarith

/-- There is at least one phase (a client exists). -/
theorem R_pos (j : Fin n) : 0 < R.P.R := by
  by_contra h
  have hR : R.P.R = 0 := by omega
  have hH : R.H = [] := List.eq_nil_of_length_eq_zero (by rw [R.sol.1, hR])
  have h1 := Sol.profL_lt_K R.good R.sol j
  rw [hH] at h1
  simp [profL, pairs, profF_empty] at h1

theorem len_pos (j : Fin n) : 0 < R.len := by
  have h1 := R.R_pos j
  have h2 : nRaise R.steps ≤ R.len := List.countP_le_length
  rw [nRaise_steps] at h2
  omega

theorem pre_succ {s : ℕ} (hs : s < R.len) :
    R.pre (s + 1) = R.pre s ++ ((R.step s).kind.atom?).toList := by
  rw [pre_eq, pre_eq, List.take_add_one, atoms_append, R.steps_getElem? hs]
  rcases hk : (R.step s).kind with a | _ <;> simp [atoms, hk, Kind.atom?]

theorem pre_len : R.pre R.len = R.H.flatten := R.pre_len'

theorem pre_prefix {s s' : ℕ} (h : s ≤ s') : R.pre s <+: R.pre s' :=
  (List.take_prefix_take_left h).filterMap _

theorem pre_sublist (s : ℕ) : List.Sublist (R.pre s) R.H.flatten := by
  rw [← pre_len, pre_eq, pre_eq, len, List.take_length]
  exact (List.take_sublist s _).filterMap _

theorem mem_pre {s : ℕ} {a : Atom m} (h : a ∈ R.pre s) : a ∈ R.H.flatten :=
  (R.pre_sublist s).subset h

theorem wf_of_mem_pre {s : ℕ} {a : Atom m} (h : a ∈ R.pre s) : a.WF R.P.K :=
  R.sol.2.2.1 a (R.mem_pre h)

theorem pairs_pre_mono {s s' : ℕ} (h : s ≤ s') : pairs (R.pre s) ⊆ pairs (R.pre s') := by
  intro q hq
  simp only [pairs, List.mem_toFinset, List.mem_map] at hq ⊢
  obtain ⟨a, ha, rfl⟩ := hq
  exact ⟨a, (R.pre_prefix h).subset ha, rfl⟩

theorem off_nonneg_of_mem_pairs {s : ℕ} {q : Fin m × ℚ} (hq : q ∈ pairs (R.pre s)) :
    0 ≤ q.2 := by
  simp only [pairs, List.mem_toFinset, List.mem_map] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  exact (R.wf_of_mem_pre ha).2.1

theorem Dpre_nonneg (s : ℕ) (j : Fin n) : 0 ≤ R.Dpre s j :=
  le_profF _ _ R.K_pos.le fun _ hq ↦
    add_nonneg (R.X.d_nonneg _ _) (R.off_nonneg_of_mem_pairs hq)

theorem Dpre_anti {s s' : ℕ} (h : s ≤ s') : R.Dpre s' ≤ R.Dpre s :=
  fun j ↦ profL_anti _ _ (R.pairs_pre_mono h) j

theorem Dpre_len : R.Dpre R.len = profL R.P.K R.X.d R.H.flatten := by
  rw [Dpre, pre_len]

/-- The time after a step is the time of the next one. -/
theorem θpost_eq {s : ℕ} (hs : s + 1 < R.len) : R.θpost s = R.θs (s + 1) := by
  rw [R.θpost_eq_θ (by omega), R.θs_eq hs]

theorem nRaise_take_mono {s s' : ℕ} (h : s ≤ s') :
    nRaise (R.steps.take s) ≤ nRaise (R.steps.take s') :=
  (List.take_sublist_take_left h).countP_le

theorem θs_mono {s s' : ℕ} (h : s ≤ s') (h' : s' < R.len) : R.θs s ≤ R.θs s' := by
  rw [R.θs_eq (by omega), R.θs_eq h']
  exact R.P.θ_mono (R.nRaise_take_mono h)

theorem θpost_mono {s s' : ℕ} (h : s ≤ s') (h' : s' < R.len) : R.θpost s ≤ R.θpost s' := by
  rw [R.θpost_eq_θ (by omega), R.θpost_eq_θ h']
  exact R.P.θ_mono (R.nRaise_take_mono (by omega))

theorem θs_le_θpost (s : ℕ) : R.θs s ≤ R.θpost s := by
  unfold θpost Par.θplus
  have := R.P.one_le_θ ((R.step s).seq / 2)
  have : R.θs s = R.P.θ ((R.step s).seq / 2) := rfl
  split_ifs <;> nlinarith [sq_nonneg R.P.ε]

theorem θpost_of_op {s : ℕ} {a : Atom m} (h : (R.step s).kind = .op a) : R.θpost s = R.θs s := by
  unfold θpost
  rw [h]
  rfl

theorem θpost_last (j : Fin n) : R.θpost (R.len - 1) = R.P.θ R.P.R := by
  have hl := R.len_pos j
  rw [R.θpost_eq_θ (by omega), Nat.sub_add_cancel hl, len, List.take_length, nRaise_steps]

theorem one_le_θs (s : ℕ) : 1 ≤ R.θs s := R.P.one_le_θ _

/-- The prefix of a step in sequence `p` is the first `p` sequences and part of `H_p`. -/
theorem exists_pre_eq {s : ℕ} (hs : s < R.len) : ∃ t, t ≤ (R.H.getD (R.step s).seq []).length ∧
    R.pre s = (R.H.take (R.step s).seq).flatten ++ (R.H.getD (R.step s).seq []).take t := by
  obtain ⟨-, t, ht, h, -⟩ := R.step_spec hs
  exact ⟨t, ht, h⟩

theorem sum_range_getD {α : Type*} (l : List α) (Q : α → Bool) (d0 : α) :
    ∑ s ∈ range l.length, (if Q (l.getD s d0) = true then 1 else 0) = l.countP Q := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ, List.countP_append]
    have h1 : ∀ s ∈ range l.length, (if Q ((l ++ [x]).getD s d0) = true then 1 else 0) =
        (if Q (l.getD s d0) = true then 1 else 0) := fun s hs ↦ by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (Finset.mem_range.1 hs)]
    rw [Finset.sum_congr rfl h1, ih, List.getD_eq_getElem?_getD,
      List.getElem?_append_right le_rfl]
    simp [List.countP_cons]

/-- Whether a step opens a regular atom. -/
def isRegStep (x : Step m) : Bool :=
  match x.kind with
  | .op a => !a.free
  | .raise => false

theorem isReg_iff (s : ℕ) : R.IsReg s ↔ isRegStep (R.step s) = true := by
  unfold IsReg isRegStep
  rcases (R.step s).kind with a | _ <;> simp

/-- The number of regular openings is the number of regular atoms. -/
theorem card_regSteps [DecidablePred R.IsReg] :
    ((range R.len).filter R.IsReg).card = nReg R.H := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h1 : ∀ s ∈ range R.len, (if R.IsReg s then 1 else 0) =
      (if isRegStep (R.steps.getD s ⟨0, .raise⟩) = true then 1 else 0) := fun s _ ↦ by
    by_cases h : R.IsReg s
    · have h' : isRegStep (R.steps.getD s ⟨0, .raise⟩) = true := (R.isReg_iff s).1 h
      rw [if_pos h, if_pos h']
    · have h' : ¬ isRegStep (R.steps.getD s ⟨0, .raise⟩) = true := mt (R.isReg_iff s).2 h
      rw [if_neg h, if_neg h']
  rw [Finset.sum_congr rfl h1, len, sum_range_getD, nReg, ← List.countP_eq_length_filter,
    ← pre_len, pre_eq, len, List.take_length, atoms, List.countP_filterMap]
  congr 1
  funext x
  unfold isRegStep
  rcases x.kind with a | _ <;> rfl

/-! ### Inactivity -/

theorem exists_inact (j : Fin n) : ∃ s, s < R.len ∧ R.Inact s j := by
  have hl := R.len_pos j
  refine ⟨R.len - 1, by omega, ?_⟩
  unfold Inact
  rw [R.θpost_last j, Nat.sub_add_cancel hl, Dpre_len]
  exact R.sol.2.2.2 j

open Classical in
theorem σ_spec (j : Fin n) : R.σ j < R.len ∧ R.Inact (R.σ j) j := by
  have h := R.exists_inact j
  unfold σ
  rw [dif_pos h]
  exact Nat.find_spec h

theorem σ_lt (j : Fin n) : R.σ j < R.len := (R.σ_spec j).1

theorem inact_σ (j : Fin n) : R.Inact (R.σ j) j := (R.σ_spec j).2

open Classical in
theorem not_inact_of_lt {s : ℕ} {j : Fin n} (h : s < R.σ j) : ¬ R.Inact s j := by
  have he := R.exists_inact j
  have hlt := R.σ_lt j
  unfold σ at h hlt
  rw [dif_pos he] at h hlt
  exact fun hi ↦ Nat.find_min he h ⟨h.trans hlt, hi⟩

theorem σ_le {s : ℕ} {j : Fin n} (h : R.Inact s j) : R.σ j ≤ s := by
  by_contra hc
  exact R.not_inact_of_lt (not_le.1 hc) h

theorem inact_mono {s s' : ℕ} {j : Fin n} (h : R.Inact s j) (hs : s ≤ s') (hs' : s' < R.len) :
    R.Inact s' j := by
  unfold Inact at h ⊢
  have h1 := R.Dpre_anti (show s + 1 ≤ s' + 1 by omega) j
  have h2 := R.θpost_mono hs hs'
  have := R.good.one_sub_δ_pos
  nlinarith

theorem Dpre_zero (j : Fin n) : R.Dpre 0 j = R.P.K := by
  change profF R.P.K R.X.d (pairs []) j = R.P.K
  exact profF_empty _ _ j

/-- Every client is active before the step at which it becomes inactive. -/
theorem active_before (j : Fin n) : R.θs (R.σ j) < (1 - R.P.δ) * R.Dpre (R.σ j) j := by
  rcases Nat.eq_zero_or_pos (R.σ j) with h | h
  · rw [h, Dpre_zero, R.θs_eq (R.len_pos j), List.take_zero]
    have := R.good.K_ge
    have := R.P.one_le_θ R.P.R
    have := R.good.δ_le
    have h1 : R.P.θ (nRaise ([] : List (Step m))) = 1 := pow_zero _
    rw [h1]
    nlinarith
  · obtain ⟨s, hs⟩ : ∃ s, R.σ j = s + 1 := ⟨R.σ j - 1, by omega⟩
    have h1 := R.not_inact_of_lt (show s < R.σ j by omega)
    unfold Inact at h1
    rw [R.θpost_eq (by rw [← hs]; exact R.σ_lt j), ← hs] at h1
    exact not_le.1 h1

/-! ### Witnesses -/

theorem pairs_sub_wit (s : ℕ) : pairs (R.pre s) ⊆ (R.wit s).1 := by
  unfold wit
  split
  · split_ifs with h1 h2 h3
    · exact subset_rfl
    · exact h3.choose_spec.choose_spec.1
    · exact subset_rfl
    · exact subset_rfl
  · exact subset_rfl

theorem Dt_le (s : ℕ) : R.Dt s ≤ R.Dpre s :=
  fun j ↦ profF_anti _ _ (R.pairs_sub_wit s) j

theorem getD_eq {p : ℕ} (hp : p < R.H.length) : R.H.getD p [] = R.H[p] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]

/-- The atom opened at step `s` is valid after the prefix. -/
theorem validAt_step {s : ℕ} {a : Atom m} (hs : s < R.len) (ha : (R.step s).kind = .op a) :
    ValidAt R.P R.X.d R.f R.P.η (R.step s).seq (R.pre s) a := by
  obtain ⟨hp, t, -, hpre, -, hat⟩ := R.step_spec hs
  have hp' : (R.step s).seq < R.H.length := by rw [R.sol.1]; exact hp
  rw [hpre]
  revert hat
  rw [R.getD_eq hp']
  intro hat
  obtain ⟨ht, hta⟩ := hat a ha
  rw [← hta]
  exact (R.sol.2.1 _ hp').1 t ht

theorem mem_of_step {s : ℕ} {a : Atom m} (hs : s < R.len) (ha : (R.step s).kind = .op a) :
    a ∈ R.H.flatten := by
  have h := R.pre_succ hs
  rw [ha] at h
  exact R.mem_pre (s := s + 1) (by rw [h]; simp [Kind.atom?])

theorem wf_of_step {s : ℕ} {a : Atom m} (hs : s < R.len) (ha : (R.step s).kind = .op a) :
    a.WF R.P.K := R.sol.2.2.1 a (R.mem_of_step hs ha)

/-- After a regular opening, every client is within its distance to the opened facility. -/
theorem Dpre_succ_le {s : ℕ} {a : Atom m} (hs : s < R.len) (ha : (R.step s).kind = .op a)
    (hreg : a.free = false) (j : Fin n) : R.Dpre (s + 1) j ≤ R.X.d j a.fac := by
  have h := R.pre_succ hs
  rw [ha] at h
  have hmem : a.pair ∈ pairs (R.pre (s + 1)) := by
    rw [h]
    simp [pairs, Kind.atom?]
  have h1 := profF_le R.P.K R.X.d hmem j
  have h2 := (R.wf_of_step hs ha).1 hreg
  simp only [Atom.pair] at h1
  rw [h2, add_zero] at h1
  exact h1

theorem exists_witOK {s : ℕ} {a : Atom m} (hs : s < R.len) (h : R.IsOp2 s a) :
    ∃ S T, R.WitOK s a S T := by
  rcases R.validAt_step hs h.1 with hf | ⟨S, hS, hS0, hO⟩
  · rw [h.2.2] at hf
    exact absurd hf (by simp)
  · simp only [OpenT, h.2.1, Bool.cond_false] at hO
    obtain ⟨T, h1, h2, h3, h4⟩ := hO
    exact ⟨S, T, hS, hS0, h1, h2, h3, h4⟩

theorem wit_spec {s : ℕ} {a : Atom m} (hs : s < R.len) (h : R.IsOp2 s a) :
    R.WitOK s a (R.wit s).1 (R.Tt s) := by
  have hex := R.exists_witOK hs h
  unfold Tt wit
  simp only [h.1, h.2.1, h.2.2, and_self, ite_true]
  by_cases h1 : ∃ T, R.WitOK s a (pairs (R.pre s)) T
  · rw [dif_pos h1]
    exact h1.choose_spec
  · rw [dif_neg h1, dif_pos hex]
    exact hex.choose_spec.choose_spec

theorem wit_eq_of_open {s : ℕ} {a : Atom m} (h : R.IsOp2 s a)
    (ho : ∃ T, R.WitOK s a (pairs (R.pre s)) T) : (R.wit s).1 = pairs (R.pre s) := by
  unfold wit
  simp only [h.1, h.2.1, h.2.2, and_self, ite_true]
  rw [dif_pos ho]

theorem wit_of_not_op2 {s : ℕ} (h : ∀ a, ¬ R.IsOp2 s a) :
    R.wit s = (pairs (R.pre s), R.θs s) := by
  unfold wit
  split
  · rename_i a ha
    rw [if_neg (fun h' ↦ h a ⟨ha, h'⟩)]
  · rfl

theorem etaValid_take {P : Par} {d : Fin n → Fin m → ℚ} {f η : ℚ}
    {H : List (List (Atom m))} (h : EtaValid P d f η H) (q : ℕ) :
    EtaValid P d f η (H.take q) := by
  intro p hp
  have hp' : p < H.length := by rw [List.length_take] at hp; omega
  have hq : p < q := by rw [List.length_take] at hp; omega
  have e1 : (H.take q).take p = H.take p := by rw [List.take_take, min_eq_left hq.le]
  rw [e1, List.getElem_take]
  exact h p hp'

/-- A regular opening collects at least `f - n η`. -/
theorem sum_contrib_ge {s : ℕ} (hs : s < R.len) (h : R.IsReg s) :
    R.f - n * R.P.η ≤ ∑ j, R.contrib j s := by
  obtain ⟨a, ha, hfree⟩ := h
  by_cases h1 : typ1 (R.step s).seq = true
  · have hw : R.wit s = (pairs (R.pre s), R.θs s) := R.wit_of_not_op2 fun b hb ↦ by
      rw [hb.2.1] at h1
      exact absurd h1 (by simp)
    have hsum : ∑ j, R.contrib j s = lhs1 R.P R.X.d (R.θs s) (R.Dpre s) a.fac := by
      have hDt : R.Dt s = R.Dpre s := by unfold Dt; rw [hw]; rfl
      unfold contrib lhs1
      simp only [ha, hfree, h1, Bool.false_eq_true, ite_false, ite_true, hDt]
    rw [hsum]
    rcases R.validAt_step hs ha with hf | ⟨S, hS, -, hO⟩
    · rw [hfree] at hf
      exact absurd hf (by simp)
    · simp only [OpenT, h1, Bool.cond_true] at hO
      exact hO.trans (lhs1_mono R.good fun j ↦ profF_anti _ _ hS j)
  · have h2 : typ1 (R.step s).seq = false := by simpa using h1
    have hw := R.wit_spec hs ⟨ha, h2, hfree⟩
    have hsum : ∑ j, R.contrib j s =
        lhs3 R.P R.X.d (R.θs s) (R.Dt s) a.fac (R.Tt s) := by
      unfold contrib lhs3
      simp only [ha, hfree, h2, Bool.false_eq_true, ite_false]
    rw [hsum]
    exact hw.2.2.2.2.1

/-! ### The values `α*` and the chains -/

theorem Dpre_succ_raise {s : ℕ} (hs : s < R.len) (h : (R.step s).kind = .raise) :
    R.Dpre (s + 1) = R.Dpre s := by
  unfold Dpre
  rw [R.pre_succ hs, h]
  simp [Kind.atom?]

theorem θpost_raise {s : ℕ} (h : (R.step s).kind = .raise) :
    R.θpost s = R.P.θplus (R.θs s) := by
  unfold θpost
  rw [h]
  rfl

theorem θs_nonneg (s : ℕ) : 0 ≤ R.θs s := zero_le_one.trans (R.one_le_θs s)

theorem θs_le_θplus (s : ℕ) : R.θs s ≤ R.P.θplus (R.θs s) := by
  unfold Par.θplus
  nlinarith [sq_nonneg R.P.ε, R.θs_nonneg s]

theorem typ1_eq_false {b : Bool} (h : ¬ b = true) : b = false := by simpa using h

theorem θs_le_αs (j : Fin n) : R.θs (R.σ j) ≤ R.αs j := by
  unfold αs
  split
  · exact (R.active_before j).le
  · split_ifs with h1 h2
    · exact le_rfl
    · exact θ_le_mT h2.le _ _
    · exact le_rfl

theorem αs_le_θplus (j : Fin n) : R.αs j ≤ R.P.θplus (R.θs (R.σ j)) := by
  have hl := R.σ_lt j
  unfold αs
  split
  · rename_i h
    have h1 := R.inact_σ j
    unfold Inact at h1
    rwa [R.Dpre_succ_raise hl h, R.θpost_raise h] at h1
  · rename_i a ha
    split_ifs with h1 h2
    · exact R.θs_le_θplus _
    · push Not at h1
      have hw := R.wit_spec hl ⟨ha, typ1_eq_false h1.1, typ1_eq_false h1.2⟩
      exact mT_le_θplus (R.θs_nonneg _) hw.2.2.2.1 _ _ _
    · exact R.θs_le_θplus _

theorem αs_le_Dpre (j : Fin n) : R.αs j ≤ (1 - R.P.δ) * R.Dpre (R.σ j) j := by
  unfold αs
  split
  · exact le_rfl
  · split_ifs with h1 h2
    · exact (R.active_before j).le
    · have := R.good.one_sub_δ_pos
      exact (mT_le_D _ _ _ _ _).trans (mul_le_mul_of_nonneg_left (R.Dt_le _ j) this.le)
    · exact (R.active_before j).le

theorem Dpre_succ_le_αs (j : Fin n) : (1 - R.P.δ) * R.Dpre (R.σ j + 1) j ≤ R.αs j := by
  have hl := R.σ_lt j
  have h1 := R.inact_σ j
  unfold Inact at h1
  rcases hk : (R.step (R.σ j)).kind with a | _
  · rw [R.θpost_of_op hk] at h1
    exact h1.trans (R.θs_le_αs j)
  · rw [R.Dpre_succ_raise hl hk]
    unfold αs
    rw [hk]

theorem αs_pos (j : Fin n) : 0 < R.αs j :=
  zero_lt_one.trans_le ((R.one_le_θs _).trans (R.θs_le_αs j))

theorem Xv_nonneg (j : Fin n) (s : ℕ) : 0 ≤ R.Xv j s := by
  unfold Xv
  split_ifs
  · exact (R.αs_pos j).le
  · exact mul_nonneg R.good.one_sub_δ_pos.le (R.Dpre_nonneg s j)

theorem Xv_of_ne {j : Fin n} {s : ℕ} (h : s ≠ R.σ j) : R.Xv j s = (1 - R.P.δ) * R.Dpre s j := by
  unfold Xv
  rw [if_neg h]

/-- [BCFGJPSSV26a, Observation E.2]: the chain is antitone after `σ j`. -/
theorem Xv_anti {j : Fin n} {s : ℕ} (h : R.σ j ≤ s) (hs : s < R.len) :
    R.Xv j (s + 1) ≤ R.Xv j s := by
  have _ := hs
  rw [R.Xv_of_ne (by omega)]
  rcases eq_or_lt_of_le h with h' | h'
  · rw [← h']
    unfold Xv
    rw [if_pos rfl]
    exact R.Dpre_succ_le_αs j
  · rw [R.Xv_of_ne (by omega)]
    exact mul_le_mul_of_nonneg_left (R.Dpre_anti (by omega) j) R.good.one_sub_δ_pos.le

theorem Xv_len (j : Fin n) : R.Xv j R.len = (1 - R.P.δ) * profL R.P.K R.X.d R.H.flatten j := by
  rw [R.Xv_of_ne (R.σ_lt j).ne', Dpre_len]

/-- [BCFGJPSSV26a, Observation E.4]. -/
theorem Zv_le_Xv {j : Fin n} {s : ℕ} (h : R.σ j ≤ s) (hs : s < R.len) : R.Zv j s ≤ R.Xv j s := by
  have _ := hs
  have hδ := R.good.one_sub_δ_pos
  have hD := mul_le_mul_of_nonneg_left (R.Dt_le s j) hδ.le
  unfold Zv
  rcases eq_or_lt_of_le h with h' | h'
  · unfold Xv
    rw [if_pos h'.symm, ← h']
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd rfl h2
    · exact (not_lt.1 h1).trans (R.θs_le_αs j)
  · rw [R.Xv_of_ne h'.ne']
    split_ifs with h1 h2
    · exact absurd h2 h'.ne
    · exact h1.le.trans hD
    · exact hD

/-- [BCFGJPSSV26a, Observation E.3]: a client bidding more than `θ` for the facility opened at
step `s` becomes inactive at `s`. -/
theorem obs_tau {s : ℕ} {a : Atom m} {j : Fin n} (hs : s < R.len) (h : R.IsOp2 s a)
    (hact : R.θs s < (1 - R.P.δ) * R.Dt s j)
    (hgt : R.θs s < mT R.P R.X.d (R.θs s) (R.Dt s) a.fac (R.Tt s) j) : R.σ j = s := by
  have hδ := R.good.one_sub_δ_pos
  apply le_antisymm
  · apply R.σ_le
    unfold Inact
    rw [R.θpost_of_op h.1]
    have h1 := le_of_θ_lt_mT hgt
    have h2 := mul_le_mul_of_nonneg_left ((R.Dpre_succ_le hs h.1 h.2.2 j).trans h1) hδ.le
    have hε := R.good.ε_le_one
    have hθ := R.θs_nonneg s
    have h3 : (1 - R.P.δ) * (R.P.ε * R.θs s) ≤ R.θs s := by
      have := R.good.δ_pos
      have := R.good.ε_pos
      have h4 : (1 - R.P.δ) * R.P.ε ≤ 1 := by nlinarith
      nlinarith
    linarith
  · by_contra hlt
    push Not at hlt
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hi := R.inact_mono (R.inact_σ j) (by omega : R.σ j ≤ s') (by omega)
    unfold Inact at hi
    rw [R.θpost_eq hs] at hi
    have := mul_le_mul_of_nonneg_left (R.Dt_le (s' + 1) j) hδ.le
    linarith

theorem contrib_nonneg (j : Fin n) (s : ℕ) : 0 ≤ R.contrib j s := by
  unfold contrib
  split
  · split_ifs
    · exact le_rfl
    · exact bid_nonneg _ _
    · exact bid_nonneg _ _
  · exact le_rfl

/-- At a regular opening of type 2, a client bids at most `θ` unless it becomes inactive. -/
theorem mT_le_θs {s : ℕ} {a : Atom m} {j : Fin n} (hs : s < R.len) (h : R.IsOp2 s a)
    (hne : R.σ j ≠ s) : mT R.P R.X.d (R.θs s) (R.Dt s) a.fac (R.Tt s) j ≤ R.θs s := by
  by_contra hc
  push Not at hc
  by_cases hact : R.θs s < (1 - R.P.δ) * R.Dt s j
  · exact hne (R.obs_tau hs h hact hc)
  · push Not at hact
    exact absurd ((mT_le_D _ _ _ _ _).trans hact) (not_le.2 hc)

/-- A client pays nothing before it becomes inactive. -/
theorem contrib_eq_zero {j : Fin n} {s : ℕ} (h : s < R.σ j) : R.contrib j s = 0 := by
  have hs : s < R.len := h.trans (R.σ_lt j)
  have hni := R.not_inact_of_lt h
  unfold Inact at hni
  push Not at hni
  have hδ := R.good.one_sub_δ_pos
  have hδ' := R.good.δ_pos
  unfold contrib
  split
  · rename_i a ha
    rw [R.θpost_of_op ha] at hni
    split_ifs with h1 h2
    · rfl
    · have hfree : a.free = false := by simpa using h1
      have h3 := mul_le_mul_of_nonneg_left (R.Dpre_succ_le hs ha hfree j) hδ.le
      refine bid_eq_zero_of_le ?_ (mul_nonneg hδ.le (R.X.d_nonneg _ _))
      exact (min_le_left _ _).trans (by linarith)
    · have hfree : a.free = false := by simpa using h1
      have hop : R.IsOp2 s a := ⟨ha, typ1_eq_false h2, hfree⟩
      have h3 := mul_le_mul_of_nonneg_left (R.Dpre_succ_le hs ha hfree j) hδ.le
      have h4 := R.mT_le_θs hs hop h.ne'
      have h5 : (1 - R.P.δ) * R.X.d j a.fac ≤ (1 - R.P.δ / 2) * R.X.d j a.fac :=
        mul_le_mul_of_nonneg_right (by linarith) (R.X.d_nonneg _ _)
      refine bid_eq_zero_of_le ?_ (mul_nonneg (by linarith) (R.X.d_nonneg _ _))
      linarith
  · rfl

/-- The value of a client that becomes inactive at a regular opening of type 2 while active
with respect to the witness. -/
theorem αs_of_op2 {j : Fin n} {a : Atom m} (h : R.IsOp2 (R.σ j) a)
    (hact : R.θs (R.σ j) < (1 - R.P.δ) * R.Dt (R.σ j) j) :
    R.αs j = mT R.P R.X.d (R.θs (R.σ j)) (R.Dt (R.σ j)) a.fac (R.Tt (R.σ j)) j := by
  unfold αs
  simp only [h.1, h.2.1, h.2.2, Bool.false_eq_true, or_self, ite_false]
  rw [if_pos hact]

/-- A value above `θ` at a regular opening of type 2 is a bid of an active client. -/
theorem αs_of_op2' {j : Fin n} {a : Atom m} (h : R.IsOp2 (R.σ j) a)
    (hgt : R.θs (R.σ j) < R.αs j) :
    R.θs (R.σ j) < (1 - R.P.δ) * R.Dt (R.σ j) j ∧
      R.αs j = mT R.P R.X.d (R.θs (R.σ j)) (R.Dt (R.σ j)) a.fac (R.Tt (R.σ j)) j := by
  by_cases hact : R.θs (R.σ j) < (1 - R.P.δ) * R.Dt (R.σ j) j
  · exact ⟨hact, R.αs_of_op2 h hact⟩
  · exfalso
    have : R.αs j = R.θs (R.σ j) := by
      unfold αs
      simp only [h.1, h.2.1, h.2.2, Bool.false_eq_true, or_self, ite_false]
      rw [if_neg hact]
    linarith

/-- After it becomes inactive, a client pays at most `β(Z_{j,s}, R_{j,s+1})`. -/
theorem contrib_le {j : Fin n} {s : ℕ} (h : R.σ j ≤ s) (hs : s < R.len) :
    R.contrib j s ≤ bid (R.Zv j s) (R.Xv j (s + 1)) := by
  have hδ := R.good.one_sub_δ_pos
  have hδ' := R.good.δ_pos
  rw [R.Xv_of_ne (by omega)]
  unfold contrib
  split
  · rename_i a ha
    split_ifs with h1 h2
    · exact bid_nonneg _ _
    · have hfree : a.free = false := by simpa using h1
      have hd := mul_le_mul_of_nonneg_left (R.Dpre_succ_le hs ha hfree j) hδ.le
      refine (bid_anti_right _ hd).trans (bid_mono_left ?_ _)
      unfold Zv mval
      split_ifs with h3 h4
      · rw [← h4]
        exact (min_le_left _ _).trans (R.θs_le_αs j)
      · exact min_le_left _ _
      · exact min_le_right _ _
    · have hfree : a.free = false := by simpa using h1
      have hop : R.IsOp2 s a := ⟨ha, typ1_eq_false h2, hfree⟩
      have hd := mul_le_mul_of_nonneg_left (R.Dpre_succ_le hs ha hfree j) hδ.le
      have hd' : (1 - R.P.δ) * R.Dpre (s + 1) j ≤ (1 - R.P.δ / 2) * R.X.d j a.fac :=
        hd.trans (mul_le_mul_of_nonneg_right (by linarith) (R.X.d_nonneg _ _))
      refine (bid_anti_right _ hd').trans (bid_mono_left ?_ _)
      unfold Zv
      split_ifs with h3 h4
      · subst h4
        rw [R.αs_of_op2 hop h3]
      · exact R.mT_le_θs hs hop h4
      · exact mT_le_D _ _ _ _ _
  · exact bid_nonneg _ _

/-! ### Freezing and far supersets -/

/-- **Freezing** ([BCFGJPSSV26a, Lemma E.8]): if client `k` with `α*_k ≥ ρ d(k, i⋆)` becomes
inactive at a regular opening of type 2 with `α*_k > θ`, and `i⋆` is a candidate before that step,
then the opened facility is within `δ θ` of `i⋆`, and every client of `D⋆` still active becomes
inactive at that step. -/
theorem freezing {istar : Fin m} {Dst : Finset (Fin n)}
    (hD : ∀ j ∈ Dst, ρ * R.X.d j istar ≤ R.αs j) {k : Fin n} (hk : k ∈ Dst) {a : Atom m}
    (hop : R.IsOp2 (R.σ k) a) (hgt : R.θs (R.σ k) < R.αs k)
    (hc : Cand R.P R.X.d R.f R.P.η (R.θs (R.σ k)) (R.Dpre (R.σ k)) istar) :
    R.X.dF istar a.fac ≤ R.P.δ * R.θs (R.σ k) ∧
      ∀ k' ∈ Dst, R.σ k ≤ R.σ k' → R.σ k' = R.σ k := by
  have hl : R.σ k < R.len := R.σ_lt k
  have hP := R.good
  have hθ1 := R.one_le_θs (R.σ k)
  have hδ := hP.one_sub_δ_pos
  have hδ' := hP.δ_pos
  have hρ : 0 < ρ := zero_lt_one.trans_le one_le_ρ
  have hγ : 0 < γ := zero_lt_one.trans_le one_le_γ
  obtain ⟨hact, hαs⟩ := R.αs_of_op2' hop hgt
  have hw := R.wit_spec hl hop
  have hnear : R.X.d k a.fac ≤ R.P.ε * R.θs (R.σ k) := le_of_θ_lt_mT (hαs ▸ hgt)
  -- the opened facility is a candidate
  have hca : Cand R.P R.X.d R.f R.P.η (R.θs (R.σ k)) (R.Dpre (R.σ k)) a.fac := by
    refine Cand.mono hP (R.θs_nonneg _) ?_ (R.Dt_le _)
    unfold Cand candSum
    refine hw.2.2.2.2.1.trans (sum_le_sum fun j _ ↦ bid_mono_left ?_ _)
    unfold cval
    split_ifs
    · exact (mT_le_T hw.2.2.1 _ _ _).trans hw.2.2.2.1
    · exact mT_le_D _ _ _ _ _
  -- maximality of the preceding sequence of type 1
  have hp := (R.step_spec hl).1
  have hodd : (R.step (R.σ k)).seq % 2 = 1 := by
    have := hop.2.1
    simp only [typ1, beq_eq_false_iff_ne, ne_eq] at this
    omega
  have hp1 : (R.step (R.σ k)).seq - 1 < R.H.length := by rw [R.sol.1]; omega
  have hmax := (R.sol.2.1 _ hp1).2
  have he1 : typ1 ((R.step (R.σ k)).seq - 1) = true := by
    simp only [typ1, beq_iff_eq]
    omega
  have he2 : R.P.θseq ((R.step (R.σ k)).seq - 1) = R.θs (R.σ k) := by
    unfold θs Par.θseq
    congr 1
    omega
  have he3 : (R.H.take ((R.step (R.σ k)).seq - 1)).flatten ++ R.H[(R.step (R.σ k)).seq - 1] =
      (R.H.take (R.step (R.σ k)).seq).flatten := by
    rw [← R.getD_eq hp1, ← flatten_take_succ]
    congr 2
    omega
  unfold Maximal at hmax
  rw [he1, he2, he3] at hmax
  have hmax' : ∀ i, ¬ Open1 R.P R.X.d R.f 0 (R.θs (R.σ k))
      (profL R.P.K R.X.d (R.H.take (R.step (R.σ k)).seq).flatten) i := hmax
  have hD0 : R.Dpre (R.σ k) ≤ profL R.P.K R.X.d (R.H.take (R.step (R.σ k)).seq).flatten := by
    intro j
    obtain ⟨t, -, hpre⟩ := R.exists_pre_eq hl
    unfold Dpre
    rw [hpre]
    refine profL_anti _ _ ?_ j
    rw [pairs_append]
    exact Finset.subset_union_left
  have hstr := structure_lemma hP R.X R.d1 (by linarith) R.fpos (R.Dpre_nonneg _) hD0 hmax' hc hca
  -- the far case is impossible
  have hfar : ¬ R.θs (R.σ k) / γ ≤ R.X.dF istar a.fac := by
    intro h
    have h1 := R.X.dF_le k istar a.fac
    have h2 := hD k hk
    have h3 := hP.freezing_ineq
    have h4 := R.αs_le_θplus k
    have e1 : R.θs (R.σ k) * ((1 + R.P.ε ^ 2) / ρ) < R.θs (R.σ k) * (1 / γ - R.P.ε) :=
      mul_lt_mul_of_pos_left h3 (by linarith)
    have e2 : R.θs (R.σ k) * (1 / γ - R.P.ε) = R.θs (R.σ k) / γ - R.P.ε * R.θs (R.σ k) := by
      ring
    have e3 : ρ * (R.θs (R.σ k) * ((1 + R.P.ε ^ 2) / ρ)) = R.P.θplus (R.θs (R.σ k)) := by
      rw [show ρ * (R.θs (R.σ k) * ((1 + R.P.ε ^ 2) / ρ)) =
        R.θs (R.σ k) * ((1 + R.P.ε ^ 2) / ρ * ρ) by ring, div_mul_cancel₀ _ hρ.ne', Par.θplus]
      ring
    have e4 : R.θs (R.σ k) * ((1 + R.P.ε ^ 2) / ρ) < R.X.d k istar := by linarith
    have e5 := mul_lt_mul_of_pos_left e4 hρ
    linarith
  have hclose := hstr.resolve_right hfar
  refine ⟨hclose, fun k' hk' hle ↦ ?_⟩
  by_contra hne
  have hlt : R.σ k < R.σ k' := lt_of_le_of_ne hle (Ne.symm hne)
  have hni := R.not_inact_of_lt hlt
  unfold Inact at hni
  push Not at hni
  rw [R.θpost_of_op hop.1] at hni
  have hd := R.Dpre_succ_le hl hop.1 hop.2.2 k'
  have hα1 := R.αs_le_Dpre k'
  have hα2 := mul_le_mul_of_nonneg_left (R.Dpre_anti (show R.σ k + 1 ≤ R.σ k' by omega) k')
    hδ.le
  have hα3 := hD k' hk'
  have htri := R.X.d_le_d_add_dF k' a.fac istar
  have hx1 := R.d1 k' a.fac
  have hd' := mul_le_mul_of_nonneg_left hd hδ.le
  -- `α*_{k'} ≤ (1 - δ) d(k', i₀)` and `θ < (1 - δ) d(k', i₀)`
  have f1 : R.αs k' ≤ (1 - R.P.δ) * R.X.d k' a.fac := by linarith
  have f2 : R.θs (R.σ k) < (1 - R.P.δ) * R.X.d k' a.fac := by linarith
  have f3 : R.P.δ * R.θs (R.σ k) < R.P.δ * ((1 - R.P.δ) * R.X.d k' a.fac) :=
    mul_lt_mul_of_pos_left f2 hδ'
  have f4 : (1 - R.P.δ + R.P.δ ^ 2) * R.X.d k' a.fac < R.X.d k' istar := by linarith
  have f5 := mul_lt_mul_of_pos_left f4 hρ
  have f6 := mul_lt_mul_of_pos_right hP.freezing_ineq₂ (show 0 < R.X.d k' a.fac by linarith)
  nlinarith

end Run

end BCFGJPSSV26.Greedy


