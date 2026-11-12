-- Prove2me | solution 1 for ActiveLanguageGeneration.Hierarchy.nonuniform_active_hierarchy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:20:32.130372+00:00
-- url     : https://prove2.me/submissions/af4641a3-df56-4a29-9ec2-e31caa638b61

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_ActiveKGeneratable
import Theorems.Thm_ActiveLanguageGeneration_Hierarchy_finite_active_hierarchy

section
set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

namespace Dev.Transport

variable {U V : Type}

/-- Image of a language along an equivalence. -/
def mapLang (e : U ≃ V) (L : Language U) : Language V :=
  ⟨e '' L.val, L.property.image e.injective.injOn⟩

def mapColl (e : U ≃ V) (C : LanguageCollection U) : LanguageCollection V :=
  mapLang e '' C

def mapGen (e : U ≃ V) (G : Generator U) : Generator V :=
  fun l => e (G (l.map e.symm))

lemma mapLang_symm (e : U ≃ V) (L : Language U) : mapLang e.symm (mapLang e L) = L := by
  apply Subtype.ext
  simp [mapLang, Set.image_image]

lemma mapColl_symm (e : U ≃ V) (C : LanguageCollection U) :
    mapColl e.symm (mapColl e C) = C := by
  simp [mapColl, Set.image_image, mapLang_symm]

lemma inputHistory_comp (e : U ≃ V) (x : ℕ → U) (n : ℕ) :
    inputHistory (fun j => e (x j)) n = (inputHistory x n).map e := by
  simp [inputHistory, List.map_map, Function.comp_def]

lemma outputAt_mapGen (e : U ≃ V) (G : Generator U) (x : ℕ → U) (n : ℕ) :
    outputAt (mapGen e G) (fun j => e (x j)) n = e (outputAt G x n) := by
  simp [outputAt, mapGen, inputHistory_comp, List.map_map, Function.comp_def]

lemma seen_comp (e : U ≃ V) (x : ℕ → U) (n : ℕ) :
    seenInputs (fun j => e (x j)) n = e '' seenInputs x n := by
  ext z
  simp only [seenInputs, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨x j, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, hj, rfl⟩

lemma prior_comp (e : U ≃ V) (G : Generator U) (x : ℕ → U) (n : ℕ) :
    priorOutputs (mapGen e G) (fun j => e (x j)) n = e '' priorOutputs G x n := by
  ext z
  simp only [priorOutputs, Set.mem_setOf_eq, Set.mem_image, outputAt_mapGen]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨outputAt G x j, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, hj, rfl⟩

lemma correctAt_map (e : U ≃ V) (mode : Repetition) (G : Generator U) (L : Language U)
    (x : ℕ → U) (n : ℕ) :
    CorrectAt mode (mapGen e G) (mapLang e L) (fun j => e (x j)) n ↔ CorrectAt mode G L x n := by
  cases mode <;>
  simp [CorrectAt, outputAt_mapGen, seen_comp, prior_comp, mapLang, e.injective.mem_set_image]

lemma isEnum_map (e : U ≃ V) (L : Language U) (x : ℕ → U) (h : IsEnumeration L x) :
    IsEnumeration (mapLang e L) (fun j => e (x j)) := by
  refine ⟨e.injective.comp h.1, ?_⟩
  simp only [mapLang, ← h.2]
  exact (Set.range_comp e x)

theorem kgen_map (e : U ≃ V) (mode : Repetition) (C : LanguageCollection U) (k : ℕ)
    (h : ActiveKGeneratable mode C k) : ActiveKGeneratable mode (mapColl e C) k := by
  obtain ⟨hk, G, hG⟩ := h
  refine ⟨hk, mapGen e G, ?_⟩
  rintro _ ⟨L, hL, rfl⟩
  obtain ⟨x, hx, hc⟩ := hG L hL
  exact ⟨fun j => e (x j), isEnum_map e L x hx, fun n hn => (correctAt_map e mode G L x n).2 (hc n hn)⟩

theorem limgen_map (e : U ≃ V) (mode : Repetition) (C : LanguageCollection U)
    (h : ActiveLimitGeneratable mode C) : ActiveLimitGeneratable mode (mapColl e C) := by
  obtain ⟨G, hG⟩ := h
  refine ⟨mapGen e G, ?_⟩
  rintro _ ⟨L, hL, rfl⟩
  obtain ⟨x, hx, t, ht, hc⟩ := hG L hL
  exact ⟨fun j => e (x j), isEnum_map e L x hx, t, ht,
    fun n hn => (correctAt_map e mode G L x n).2 (hc n hn)⟩

theorem kgen_iff (e : U ≃ V) (mode : Repetition) (C : LanguageCollection U) (k : ℕ) :
    ActiveKGeneratable mode (mapColl e C) k ↔ ActiveKGeneratable mode C k := by
  refine ⟨fun h => ?_, kgen_map e mode C k⟩
  have := kgen_map e.symm mode _ k h
  rwa [mapColl_symm] at this

theorem limgen_iff (e : U ≃ V) (mode : Repetition) (C : LanguageCollection U) :
    ActiveLimitGeneratable mode (mapColl e C) ↔ ActiveLimitGeneratable mode C := by
  refine ⟨fun h => ?_, limgen_map e mode C⟩
  have := limgen_map e.symm mode _ h
  rwa [mapColl_symm] at this

end Dev.Transport
end ActiveLanguageGeneration.Hierarchy
end

section
set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

namespace Dev.Glue

variable {U : Type}

/-- Tag a language with the index `m`. -/
def emb (m : ℕ) (L : Language U) : Language (ℕ × U) :=
  ⟨(fun z => (m, z)) '' L.val, L.property.image (Prod.mk_right_injective m).injOn⟩

def glue (C : ℕ → LanguageCollection U) : LanguageCollection (ℕ × U) :=
  {L' | ∃ m, 2 ≤ m ∧ ∃ L ∈ C m, L' = emb m L}

lemma mem_emb (m : ℕ) (L : Language U) (m' : ℕ) (z : U) :
    (m', z) ∈ (emb m L).val ↔ m' = m ∧ z ∈ L.val := by
  simp only [emb, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨w, hw, rfl, rfl⟩; exact ⟨rfl, hw⟩
  · rintro ⟨rfl, h⟩; exact ⟨z, h, rfl, rfl⟩

lemma seen_pair (m : ℕ) (x : ℕ → U) (n : ℕ) :
    seenInputs (fun j => (m, x j)) n = (fun z => (m, z)) '' seenInputs x n := by
  ext z
  simp only [seenInputs, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨x j, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, hj, rfl⟩

lemma prior_pair (H : Generator (ℕ × U)) (G : Generator U) (m : ℕ)
    (h : ∀ (x : ℕ → U) (n : ℕ), outputAt H (fun j => (m, x j)) n = (m, outputAt G x n))
    (x : ℕ → U) (n : ℕ) :
    priorOutputs H (fun j => (m, x j)) n = (fun z => (m, z)) '' priorOutputs G x n := by
  ext z
  simp only [priorOutputs, Set.mem_setOf_eq, Set.mem_image, h]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨outputAt G x j, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, hj, rfl⟩

lemma correct_pair (mode : Repetition) (H : Generator (ℕ × U)) (G : Generator U) (m : ℕ)
    (h : ∀ (x : ℕ → U) (n : ℕ), outputAt H (fun j => (m, x j)) n = (m, outputAt G x n))
    (L : Language U) (x : ℕ → U) (n : ℕ) :
    CorrectAt mode H (emb m L) (fun j => (m, x j)) n ↔ CorrectAt mode G L x n := by
  have inj : Function.Injective (fun z : U => (m, z)) := Prod.mk_right_injective m
  cases mode <;>
  simp [CorrectAt, h, seen_pair, prior_pair H G m h, emb, inj.mem_set_image]

lemma enum_pair (m : ℕ) (L : Language U) (x : ℕ → U) (hx : IsEnumeration L x) :
    IsEnumeration (emb m L) (fun j => (m, x j)) := by
  refine ⟨fun a b hab => hx.1 (Prod.mk.inj hab).2, ?_⟩
  have := Set.range_comp (fun z : U => (m, z)) x
  simp only [emb]
  rw [← hx.2]
  exact this

lemma limit_glue [Nonempty U] (C : ℕ → LanguageCollection U)
    (hC : ∀ m, 2 ≤ m → ActiveKGeneratable .NR (C m) m) :
    ActiveLimitGeneratable .NR (glue C) := by
  classical
  have : ∀ m, ∃ G : Generator U, 2 ≤ m → ∀ L ∈ C m, ∃ x : ℕ → U,
      IsEnumeration L x ∧ ∀ n : ℕ, m ≤ n + 1 → CorrectAt .NR G L x n := by
    intro m
    by_cases hm : 2 ≤ m
    · obtain ⟨_, G, hG⟩ := hC m hm
      exact ⟨G, fun _ => hG⟩
    · exact ⟨fun _ => Classical.arbitrary U, fun h => absurd h hm⟩
  choose G hG using this
  let H : Generator (ℕ × U) := fun l =>
    match l with
    | [] => (0, Classical.arbitrary U)
    | a :: _ => (a.1, G a.1 (l.map Prod.snd))
  have hout : ∀ (m : ℕ) (x : ℕ → U) (n : ℕ),
      outputAt H (fun j => (m, x j)) n = (m, outputAt (G m) x n) := by
    intro m x n
    simp [outputAt, inputHistory, List.range_succ_eq_map, H, Function.comp_def]
  refine ⟨H, ?_⟩
  rintro _ ⟨m, hm, L, hL, rfl⟩
  obtain ⟨x, hx, hc⟩ := hG m hm L hL
  exact ⟨fun j => (m, x j), enum_pair m L x hx, m, by omega,
    fun n hn => (correct_pair .NR H (G m) m (hout m) L x n).2 (hc n hn)⟩

lemma not_glue [Nonempty U] (C : ℕ → LanguageCollection U)
    (hC : ∀ m, 2 ≤ m → ¬ ActiveKGeneratable .R (C m) (m - 1)) (k : ℕ) (hk : 0 < k) :
    ¬ ActiveKGeneratable .R (glue C) k := by
  classical
  rintro ⟨_, H, hH⟩
  apply hC (k + 1) (by omega)
  refine ⟨by omega, fun l =>
    if (H (l.map fun z => (k + 1, z))).1 = k + 1 then (H (l.map fun z => (k + 1, z))).2
    else Classical.arbitrary U, ?_⟩
  intro L hL
  obtain ⟨x', hx', hc⟩ := hH (emb (k + 1) L) ⟨k + 1, by omega, L, hL, rfl⟩
  have h1 : ∀ n, (x' n).1 = k + 1 := by
    intro n
    have : x' n ∈ (emb (k + 1) L).val := hx'.2 ▸ ⟨n, rfl⟩
    obtain ⟨w, _, hw⟩ := this
    rw [← hw]
  set x : ℕ → U := fun n => (x' n).2 with hxdef
  have hxx : x' = fun j => (k + 1, x j) := funext fun j => Prod.ext (h1 j) rfl
  refine ⟨x, ⟨fun a b hab => hx'.1 (by rw [hxx]; exact congrArg _ hab), ?_⟩, ?_⟩
  · ext z
    constructor
    · rintro ⟨n, rfl⟩
      have : x' n ∈ (emb (k + 1) L).val := hx'.2 ▸ ⟨n, rfl⟩
      rw [hxx] at this
      exact ((mem_emb _ _ _ _).1 this).2
    · intro hz
      have : (k + 1, z) ∈ (emb (k + 1) L).val := (mem_emb _ _ _ _).2 ⟨rfl, hz⟩
      rw [← hx'.2] at this
      obtain ⟨n, hn⟩ := this
      exact ⟨n, congrArg Prod.snd hn⟩
  · intro n hn
    have hc' := hc n (by omega)
    have hhist : inputHistory x' n = (inputHistory x n).map fun z => (k + 1, z) := by
      rw [hxx]
      simp [inputHistory, List.map_map, Function.comp_def]
    obtain ⟨hmem, hnot⟩ := hc'
    have hHo : H (inputHistory x' n) = outputAt H x' n := rfl
    generalize outputAt H x' n = o at hHo hmem hnot
    obtain ⟨m', z⟩ := o
    obtain ⟨rfl, hzL⟩ := (mem_emb _ _ _ _).1 hmem
    rw [hxx, seen_pair] at hnot
    have hzs : z ∉ seenInputs x n := fun hz => hnot ⟨z, hz, rfl⟩
    show outputAt _ x n ∈ L.val \ seenInputs x n
    simp only [outputAt, ← hhist, hHo]
    simp [hzL, hzs]

end Dev.Glue

/-- Theorem 4.2, printed p.20 (PDF p.21): the same collection fails every finite
positive R threshold, while one generator succeeds eventually without repetition. -/
theorem chk_nonuniform_active_hierarchy (U : Type) [Countable U] [Infinite U] :
    ∃ C : LanguageCollection U, ActiveLimitGeneratable .NR C ∧
      ∀ k : ℕ, 0 < k → ¬ ActiveKGeneratable .R C k := by
  haveI : Nonempty U := Infinite.nonempty U
  have h : ∀ m : ℕ, ∃ C : LanguageCollection U, 2 ≤ m →
      ActiveKGeneratable .NR C m ∧ ¬ ActiveKGeneratable .R C (m - 1) := by
    intro m
    by_cases hm : 2 ≤ m
    · obtain ⟨C, hC⟩ := finite_active_hierarchy U m hm
      exact ⟨C, fun _ => hC⟩
    · exact ⟨∅, fun h => absurd h hm⟩
  choose C hC using h
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ × U) (β := U)
  refine ⟨Dev.Transport.mapColl e (Dev.Glue.glue C), ?_, ?_⟩
  · exact (Dev.Transport.limgen_iff e _ _).2
      (Dev.Glue.limit_glue C fun m hm => (hC m hm).1)
  · intro k hk h
    exact Dev.Glue.not_glue C (fun m hm => (hC m hm).2) k hk
      ((Dev.Transport.kgen_iff e _ _ k).1 h)

end ActiveLanguageGeneration.Hierarchy
end

theorem solution : type_of% @ActiveLanguageGeneration.Hierarchy.chk_nonuniform_active_hierarchy := @ActiveLanguageGeneration.Hierarchy.chk_nonuniform_active_hierarchy
