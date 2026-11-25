-- Prove2me | Definitions.Def_DetDLP_W3C_Stage2Trace
-- name    : DetDLP_W3C_Stage2Trace
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:08:17.410782+00:00
-- url     : https://prove2.me/theorems/19b196dd-8e73-40ad-ab8b-caa4e9429865
-- title:
--   Stage II coset initialization and bounded halving trace
-- statement:
--   **Stage II trace theorem.** Let $N$ be the number of factor-base coordinates, and let $z\in(\mathbb Z/M\mathbb Z)^N$ satisfy the initialization rows and every valid shift equation. Under `w3_hnfOps`, initialization from the identity basis preserves $z$ in the represented coset. For an injective fixed-width pair encoding, positive root mass yields a violated shift by prefix descent. Its exact HNF intersection retains $z$ and satisfies $2|C_{\mathrm{new}}|\le |C_{\mathrm{old}}|$. Since $1\le |C|\le M^N$, at most $\lceil\log_2(M^N)\rceil$ cuts suffice to reach zero root mass. The final representative passes every valid shift, yielding a `w3_Outcome` certificate common to the multiplicative and elliptic-curve drivers.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_PrefixDescent

set_option autoImplicit false
namespace DetDLP.W3C.Stage2Trace

variable {M N : ℕ} [NeZero M]

/-- A valid basis whose represented solutions still include the true label. -/
def Invariant (z : w3_Label M N) (s : w3_Rep M N) : Prop :=
  IsModularLatticeBasis M s.2 ∧ z ∈ w3_coset s

theorem full (z : w3_Label M N) : Invariant z (w3_full M N) := by
  constructor
  · change IsColumnHNF (1 : Matrix (Fin N) (Fin N) ℤ) ∧ _ ∧ _
    refine ⟨⟨fun i j h => ?_, fun i => ?_, fun i j h => ?_⟩, fun v => ?_, ?_⟩
    · simp [h.ne]
    · simp
    · simp [h.ne']
    · exact ⟨_, (Matrix.one_mulVec _).symm⟩
    · simp [w3_full]
  · refine ⟨fun i => ((z i).val : ℤ), fun i => ?_⟩
    simp [w3_full]

theorem card_bounds {z : w3_Label M N} {s : w3_Rep M N} (hz : z ∈ w3_coset s) :
    1 ≤ Nat.card (w3_coset s) ∧ Nat.card (w3_coset s) ≤ M^N := by
  let _ : Nonempty (w3_coset s) := ⟨⟨z,hz⟩⟩
  refine ⟨Nat.card_pos, ?_⟩
  simpa [Nat.card_pi, Nat.card_zmod] using
    Nat.card_le_card_of_injective (Subtype.val : w3_coset s → w3_Label M N) Subtype.val_injective

theorem preserve {z : w3_Label M N} {s t : w3_Rep M N} {r : w3_Row M N}
    (hz : z ∈ w3_coset s) (hr : w3_holds r z) (u : w3_update r s t) : Invariant z t :=
  ⟨u.1, u.2.symm ▸ (show z ∈ {x ∈ w3_coset s | w3_holds r x} from ⟨hz,hr⟩)⟩

/-- Initialization needs consistency, not a strict decrease in size. -/
theorem initTrace (ops : w3_hnfOps) (hM : 2 ≤ M) (hN : 1 ≤ N) (z : w3_Label M N)
    (rows : List (w3_Row M N)) (holds : ∀ r ∈ rows, w3_holds r z)
    (s : w3_Rep M N) (hs : Invariant z s) : ∃ t, w3_InitTrace rows s t ∧ Invariant z t := by
  obtain ⟨_,_,_,op⟩ := ops
  induction rows generalizing s with
  | nil => exact ⟨s,.nil s,hs⟩
  | cons r rs ih =>
    have hr := holds r List.mem_cons_self
    obtain ⟨t,hu,_,_⟩ := op M N hM hN s r hs.1 ⟨z,hs.2,hr⟩
    obtain ⟨v,hv,hi⟩ := ih (fun a ha => holds a (List.mem_cons_of_mem _ ha)) t (preserve hs.2 hr hu)
    exact ⟨v,.cons hu hv,hi⟩

variable (q : w3_Query) {L : ℕ}
private abbrev Rep := w3_Rep q.M q.FB.totalCoords
private abbrev Label := w3_Label q.M q.FB.totalCoords

/-- Query at the empty prefix for the current coset representative. -/
def root (s : Rep q) : w3_Query := {q with y := s.1, pre := []}

variable (ops : w3_hnfOps) (hM : 2 ≤ q.M) (width : ∀ X Y, (q.code X Y).length = L)
    (inj : Function.Injective (Function.uncurry q.code)) (z : Label q) (pass : w3_pass q.FB q.M q.P z)
include ops hM width inj pass

theorem stop_or_cut (s : Rep q) (hs : Invariant z s) :
    w3_mass (root q s) = 0 ∨ ∃ t, w3_cut q.FB q.M q.P s t ∧ Invariant z t := by
  by_cases h : w3_mass (root q s) = 0
  · exact .inl h
  right
  have hn := w3c_mass_nonneg (root q s)
  have hp : 0 < w3_mass (root q s) := by omega
  obtain ⟨_,_,⟨X,Y⟩,⟨_,hg,hw,hbad⟩,_⟩ := w3c_descent (root q s) width inj hM hp
  have hr := pass X Y hg
  obtain ⟨_,_,_,op⟩ := ops
  obtain ⟨t,hu,half,_⟩ := op q.M _ hM q.FB.genCoord.pos s _ hs.1 ⟨z,hs.2,hr⟩
  exact ⟨t,⟨X,Y,hg,hw,hbad,hu,half hbad⟩,preserve hs.2 hr hu⟩

/-- With `k` cuts left, size at most `2^k` suffices. At zero budget a further
    cut would leave at least one solution in a coset of size at most one half. -/
theorem bounded (k : ℕ) (s : Rep q) (hs : Invariant z s) (cap : Nat.card (w3_coset s) ≤ 2^k) :
    ∃ n t, n ≤ k ∧ w3_Cuts q.FB q.M q.P n s t ∧ Invariant z t ∧ w3_mass (root q t) = 0 := by
  induction k generalizing s with
  | zero =>
    rcases stop_or_cut q ops hM width inj z pass s hs with h | ⟨t,hcut,ht⟩
    · exact ⟨0,s,le_rfl,.nil s,hs,h⟩
    · obtain ⟨_,_,_,_,_,_,hh⟩ := hcut
      have := (card_bounds ht.2).1
      simp only [pow_zero] at cap
      omega
  | succ k ih =>
    rcases stop_or_cut q ops hM width inj z pass s hs with h | ⟨t,hcut,ht⟩
    · exact ⟨0,s,Nat.zero_le _,.nil s,hs,h⟩
    · have ⟨_,_,_,_,_,_,hh⟩ := hcut
      rw [pow_succ] at cap
      obtain ⟨n,u,hn,hc,hi,hz⟩ := ih t ht (by omega)
      exact ⟨n+1,u,Nat.succ_le_succ hn,.cons hcut hc,hi,hz⟩

/-- Shared Stage II certificate for any native query with fixed-width injective codes. -/
theorem outcome (U : Fin q.FB.totalCoords → q.FB.BlockTuple)
    (holds : ∀ r ∈ w3_initRows q.FB q.M U, w3_holds r z) :
    ∃ t : Rep q, Invariant z t ∧ w3_mass (root q t) = 0 ∧ w3_Outcome q.FB q.M q.P U t.1 := by
  obtain ⟨s,hs,hi⟩ := initTrace ops hM q.FB.genCoord.pos z _ holds _ (full z)
  obtain ⟨n,t,hn,hc,ht,hz⟩ := bounded q ops hM width inj z pass _ s hi
    ((card_bounds hi.2).2.trans (Nat.le_pow_clog (by decide : 1 < 2) _))
  exact ⟨t,ht,hz,s,t,n,hs,hc,hn,rfl,w3c_zero_pass (root q t) rfl hz⟩

end DetDLP.W3C.Stage2Trace


