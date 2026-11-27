-- Prove2me | solution 1 for AlonMilman.PropertyT.Supplement.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:59.564726+00:00
-- url     : https://prove2.me/submissions/fb0e3b79-9989-4b16-a5a5-34eb8da485d6

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AlonMilman_PropertyT_Supplement_boxPi

open AlonMilman
open AlonMilman.PropertyT
open AlonMilman.PropertyT.Supplement

/-- Proposition 3.1 (Alon–Milman 1985, pp. 80–81). Let `G_1, …, G_l` (`l ≥ 1`) be finite
connected simple graphs with diameters `ρ_j`, maximal degrees `d_j` and `λ_j = λ₁(G_j)`, and let
`G` be their Cartesian product. Then `diam G = ∑ ρ_j`, the maximal degree of `G` is `∑ d_j`, and,
when every factor has at least two vertices (so that each `λ_j` is defined),
`λ₁(G) = min_j λ_j`. -/
theorem solution {l : ℕ} (hl : 0 < l) {W : Fin l → Type} [∀ j, Fintype (W j)]
    [∀ j, DecidableEq (W j)] (G : ∀ j, SimpleGraph (W j)) [∀ j, DecidableRel (G j).Adj]
    (hG : ∀ j, (G j).Connected) :
    (boxPi G).diam = ∑ j, (G j).diam ∧
    (boxPi G).maxDegree = ∑ j, (G j).maxDegree ∧
    ((∀ j, 2 ≤ Fintype.card (W j)) →
      AlonMilman.Diameter.lambda1 (boxPi G) =
        Finset.univ.inf' ⟨⟨0, hl⟩, Finset.mem_univ _⟩
          (fun j => AlonMilman.Diameter.lambda1 (G j))) := by
            classical
            have hne : ∀ j, Nonempty (W j) := fun j => (hG j).nonempty
            -- adjacency of updates
            have adj_upd : ∀ (x : ∀ j, W j) (j : Fin l) (a b : W j), (G j).Adj a b →
                (boxPi G).Adj (Function.update x j a) (Function.update x j b) := by
              intro x j a b h
              refine ⟨j, by simpa using h, fun j' hj' => ?_⟩
              simp [Function.update_of_ne hj']
            -- walks: upper bound on distance
            have walk_ub : ∀ (s : Finset (Fin l)) (x y : ∀ j, W j), (∀ j ∉ s, x j = y j) →
                ∃ p : (boxPi G).Walk x y, p.length ≤ ∑ j ∈ s, (G j).dist (x j) (y j) := by
              intro s
              induction s using Finset.induction_on with
              | empty =>
                intro x y h
                have : x = y := funext fun j => h j (Finset.notMem_empty j)
                subst this
                exact ⟨SimpleGraph.Walk.nil, by simp⟩
              | insert j s hj ih =>
                intro x y h
                set z := Function.update x j (y j) with hz
                obtain ⟨q, hq⟩ := ih z y (by
                  intro k hk
                  by_cases hkj : k = j
                  · subst hkj; simp [hz]
                  · simp only [hz, Function.update_of_ne hkj]
                    exact h k (by simp [hkj, hk]))
                obtain ⟨r, hr⟩ := (hG j).exists_walk_length_eq_dist (x j) (y j)
                let ι : G j →g boxPi G :=
                  { toFun := fun w => Function.update x j w
                    map_rel' := fun {a b} hab => adj_upd x j a b hab }
                let r' : (boxPi G).Walk x z := (r.map ι).copy (by simp [ι]) (by simp [ι, hz])
                refine ⟨r'.append q, ?_⟩
                rw [SimpleGraph.Walk.length_append, Finset.sum_insert hj]
                have hzs : ∑ k ∈ s, (G k).dist (z k) (y k) = ∑ k ∈ s, (G k).dist (x k) (y k) := by
                  refine Finset.sum_congr rfl fun k hk => ?_
                  have hkj : k ≠ j := fun e => hj (e ▸ hk)
                  simp [hz, Function.update_of_ne hkj]
                have : r'.length = (G j).dist (x j) (y j) := by
                  simp [r', hr]
                omega
            have conn : (boxPi G).Connected := by
              refine SimpleGraph.Connected.mk ?_
              intro x y
              obtain ⟨p, -⟩ := walk_ub Finset.univ x y (by simp)
              exact ⟨p⟩
            have dist_ub : ∀ x y : (∀ j, W j), (boxPi G).dist x y ≤ ∑ j, (G j).dist (x j) (y j) := by
              intro x y
              obtain ⟨p, hp⟩ := walk_ub Finset.univ x y (by simp)
              exact (SimpleGraph.dist_le p).trans hp
            have walk_lb : ∀ (x y : ∀ j, W j) (p : (boxPi G).Walk x y),
                ∑ j, (G j).dist (x j) (y j) ≤ p.length := by
              intro x y p
              induction p with
              | nil => simp
              | @cons x z y h p ih =>
                rw [SimpleGraph.Walk.length_cons]
                obtain ⟨i, hi, hi'⟩ := id h
                have key : ∀ k, (G k).dist (x k) (y k) ≤ (G k).dist (z k) (y k) + if k = i then 1 else 0 := by
                  intro k
                  by_cases hk : k = i
                  · subst hk
                    have := (hG k).dist_triangle (u := x k) (v := z k) (w := y k)
                    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hi] at this
                    simp; omega
                  · simp [hk, hi' k hk]
                calc ∑ j, (G j).dist (x j) (y j) ≤ ∑ j, ((G j).dist (z j) (y j) + if j = i then 1 else 0) :=
                      Finset.sum_le_sum fun k _ => key k
                  _ = ∑ j, (G j).dist (z j) (y j) + 1 := by rw [Finset.sum_add_distrib]; simp
                  _ ≤ p.length + 1 := by omega
            have dist_eq : ∀ x y : (∀ j, W j), (boxPi G).dist x y = ∑ j, (G j).dist (x j) (y j) := by
              intro x y
              refine le_antisymm (dist_ub x y) ?_
              obtain ⟨p, hp⟩ := conn.exists_walk_length_eq_dist x y
              rw [← hp]; exact walk_lb x y p
            have part1 : (boxPi G).diam = ∑ j, (G j).diam := by
              have hfin : (boxPi G).ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp conn
              have hfinj : ∀ j, (G j).ediam ≠ ⊤ := fun j => SimpleGraph.connected_iff_ediam_ne_top.mp (hG j)
              apply le_antisymm
              · obtain ⟨u, v, huv⟩ := (boxPi G).exists_dist_eq_diam
                rw [← huv, dist_eq]
                exact Finset.sum_le_sum fun j _ => SimpleGraph.dist_le_diam (hfinj j)
              · choose u v huv using fun j => (G j).exists_dist_eq_diam
                calc ∑ j, (G j).diam = ∑ j, (G j).dist (u j) (v j) := by simp [huv]
                  _ = (boxPi G).dist u v := (dist_eq u v).symm
                  _ ≤ _ := SimpleGraph.dist_le_diam hfin
            have NB : ∀ (x : ∀ j, W j) (g : (∀ j, W j) → ℝ),
                ∑ y ∈ (boxPi G).neighborFinset x, g y =
                  ∑ j, ∑ w ∈ (G j).neighborFinset (x j), g (Function.update x j w) := by
              intro x g
              rw [← Finset.sum_sigma (s := Finset.univ) (t := fun j => (G j).neighborFinset (x j))
                (f := fun p => g (Function.update x p.1 p.2))]
              symm
              refine Finset.sum_bij (fun p _ => Function.update x p.1 p.2) ?_ ?_ ?_ ?_
              · rintro ⟨j, w⟩ hp
                simp only [Finset.mem_sigma, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset] at hp ⊢
                have := adj_upd x j (x j) w hp
                simpa using this
              · rintro ⟨j, w⟩ hp ⟨j', w'⟩ hp' heq
                simp only [Finset.mem_sigma, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset] at hp hp' heq
                by_cases hjj : j = j'
                · subst hjj
                  have := congrFun heq j
                  simp at this
                  subst this; rfl
                · exfalso
                  have := congrFun heq j
                  rw [Function.update_self, Function.update_of_ne hjj] at this
                  exact (G j).irrefl (this ▸ hp)
              · intro y hy
                simp only [SimpleGraph.mem_neighborFinset] at hy
                obtain ⟨j, hj, hj'⟩ := id hy
                refine ⟨⟨j, y j⟩, by simpa using hj, ?_⟩
                funext k
                by_cases hk : k = j
                · subst hk; simp
                · simp [Function.update_of_ne hk, hj' k hk]
              · intro _ _; rfl
            have deg_eq : ∀ x : (∀ j, W j), (boxPi G).degree x = ∑ j, (G j).degree (x j) := by
              intro x
              have := NB x (fun _ => 1)
              simp only [Finset.sum_const, nsmul_eq_mul, mul_one, SimpleGraph.card_neighborFinset_eq_degree] at this
              exact_mod_cast this
            have part2 : (boxPi G).maxDegree = ∑ j, (G j).maxDegree := by
              apply le_antisymm
              · apply SimpleGraph.maxDegree_le_of_forall_degree_le
                intro x; rw [deg_eq]
                exact Finset.sum_le_sum fun j _ => (G j).degree_le_maxDegree (x j)
              · choose u hu using fun j => (G j).exists_maximal_degree_vertex
                calc ∑ j, (G j).maxDegree = ∑ j, (G j).degree (u j) := by simp [hu]
                  _ = (boxPi G).degree u := (deg_eq u).symm
                  _ ≤ _ := (boxPi G).degree_le_maxDegree u
            refine ⟨part1, part2, ?_⟩
            intro hcard
            have SYM : ∀ (V : Type) [Fintype V] (A : Matrix V V ℝ), (∀ x y, A x y = A y x) →
                ∀ g h : V → ℝ, ∑ x, (Matrix.mulVec A g) x * h x = ∑ x, g x * (Matrix.mulVec A h) x := by
              intro V _ A hA g h
              simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
              rw [hA]; ring
            have GEN : ∀ (V S : Type) [Fintype V] [Fintype S] [DecidableEq V] (A : Matrix V V ℝ)
                (Φ : S → V → ℝ) (μ : S → ℝ), (∀ x y, A x y = A y x) → (∀ s, Matrix.mulVec A (Φ s) = μ s • Φ s) →
                (∀ x y, ∑ s, Φ s x * Φ s y = if x = y then 1 else 0) → ∀ f : V → ℝ,
                ∑ x, f x * f x = ∑ s, (∑ x, Φ s x * f x) ^ 2 ∧
                ∑ x, f x * (Matrix.mulVec A f) x = ∑ s, μ s * (∑ x, Φ s x * f x) ^ 2 := by
              intro V S _ _ _ A Φ μ hA heig hcomp f
              obtain ⟨c, hc⟩ : ∃ c : S → ℝ, ∀ s, ∑ x, Φ s x * f x = c s := ⟨_, fun _ => rfl⟩
              simp only [hc]
              have hf : ∀ x, ∑ s, c s * Φ s x = f x := by
                intro x
                simp only [← hc, Finset.sum_mul]
                rw [Finset.sum_comm]
                calc ∑ y, ∑ s, Φ s y * f y * Φ s x = ∑ y, f y * ∑ s, Φ s y * Φ s x := by
                       refine Finset.sum_congr rfl fun y _ => ?_
                       rw [Finset.mul_sum]
                       refine Finset.sum_congr rfl fun s _ => ?_; ring
                  _ = f x := by simp [hcomp]
              have expand : ∀ g : V → ℝ, ∑ x, f x * g x = ∑ s, c s * ∑ x, Φ s x * g x := by
                intro g
                calc ∑ x, f x * g x = ∑ x, (∑ s, c s * Φ s x) * g x := by simp [hf]
                  _ = ∑ s, c s * ∑ x, Φ s x * g x := by
                      simp only [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun x _ => ?_; ring
              constructor
              · rw [expand f]; simp [hc, sq]
              · rw [expand]
                refine Finset.sum_congr rfl fun s _ => ?_
                rw [← SYM V A hA, heig s]
                simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hc]; ring
            have TWO : ∀ (V S : Type) [Fintype V] [Fintype S] [DecidableEq S] (A : Matrix V V ℝ)
                (Φ : S → V → ℝ) (μ : S → ℝ), (∀ s, Matrix.mulVec A (Φ s) = μ s • Φ s) →
                (∀ s t, ∑ x, Φ s x * Φ t x = if s = t then 1 else 0) → ∀ s t, s ≠ t → ∀ a b : ℝ,
                ∑ x, (a * Φ s x + b * Φ t x) * (a * Φ s x + b * Φ t x) = a ^ 2 + b ^ 2 ∧
                ∑ x, (a * Φ s x + b * Φ t x) * (Matrix.mulVec A (fun x => a * Φ s x + b * Φ t x)) x
                  = a ^ 2 * μ s + b ^ 2 * μ t := by
              intro V S _ _ _ A Φ μ heig horth s t hst a b
              have hAf : Matrix.mulVec A (fun x => a * Φ s x + b * Φ t x) = fun x => a * μ s * Φ s x + b * μ t * Φ t x := by
                have : (fun x => a * Φ s x + b * Φ t x) = a • Φ s + b • Φ t := by
                  funext x; simp
                rw [this, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, heig, heig]
                funext x; simp; ring
              rw [hAf]
              have hst' : t ≠ s := fun e => hst e.symm
              constructor
              · have e : ∀ x, (a * Φ s x + b * Φ t x) * (a * Φ s x + b * Φ t x) =
                    a ^ 2 * (Φ s x * Φ s x) + (2 * a * b) * (Φ s x * Φ t x) + b ^ 2 * (Φ t x * Φ t x) := by
                  intro x; ring
                simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, horth]
                simp [hst]
              · have e : ∀ x, (a * Φ s x + b * Φ t x) * (a * μ s * Φ s x + b * μ t * Φ t x) =
                    (a ^ 2 * μ s) * (Φ s x * Φ s x) + (a * b * (μ s + μ t)) * (Φ s x * Φ t x) +
                      (b ^ 2 * μ t) * (Φ t x * Φ t x) := by
                  intro x; ring
                simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, horth]
                simp [hst]
            have PICK : ∀ p q : ℝ, ∃ a b : ℝ, a * p + b * q = 0 ∧ 0 < a ^ 2 + b ^ 2 := by
              intro p q
              by_cases h : p = 0 ∧ q = 0
              · exact ⟨1, 0, by simp [h.1, h.2], by norm_num⟩
              · refine ⟨q, -p, by ring, ?_⟩
                rcases not_and_or.mp h with h | h
                · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg q]
                · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg p]
            have SPEC : ∀ (V : Type) [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) (hA : A.PosSemidef)
                (h2 : 2 ≤ Fintype.card V), ∃ (Φ : V → V → ℝ) (μ : V → ℝ) (bot sec : V),
                (∀ x y, A x y = A y x) ∧ (∀ s, Matrix.mulVec A (Φ s) = μ s • Φ s) ∧
                (∀ s t, ∑ x, Φ s x * Φ t x = if s = t then 1 else 0) ∧
                (∀ x y, ∑ s, Φ s x * Φ s y = if x = y then 1 else 0) ∧ (∀ s, 0 ≤ μ s) ∧ bot ≠ sec ∧
                μ sec = hA.isHermitian.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ ∧
                (∀ s, s ≠ bot → μ sec ≤ μ s) ∧ μ bot ≤ μ sec := by
              intro V _ _ A hA h2
              set hH := hA.isHermitian
              set b := hH.eigenvectorBasis
              let e : Fin (Fintype.card V) ≃ V := Fintype.equivOfCardEq (Fintype.card_fin _)
              have hμ : ∀ s, hH.eigenvalues s = hH.eigenvalues₀ (e.symm s) := fun s => rfl
              refine ⟨fun s x => (b s).ofLp x, hH.eigenvalues, e ⟨Fintype.card V - 1, by omega⟩,
                e ⟨Fintype.card V - 2, by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · intro x y
                have := hH.apply x y
                simpa using this.symm
              · intro s; exact hH.mulVec_eigenvectorBasis s
              · intro s t
                have := orthonormal_iff_ite.mp b.orthonormal s t
                rw [← this]
                simp [PiLp.inner_apply, mul_comm]
              · intro x y
                have := b.sum_inner_mul_inner (EuclideanSpace.single x 1) (EuclideanSpace.single y 1)
                simp [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] at this
                show ∑ s, (b s).ofLp x * (b s).ofLp y = _
                rw [this]; exact if_congr eq_comm rfl rfl
              · intro s; exact hA.eigenvalues_nonneg s
              · intro h
                have := e.injective h
                simp [Fin.ext_iff] at this; omega
              · rw [hμ]; simp
              · intro s hs
                rw [hμ, hμ, Equiv.symm_apply_apply]
                apply hH.eigenvalues₀_antitone
                have : e.symm s ≠ ⟨Fintype.card V - 1, by omega⟩ := by
                  intro h; apply hs; rw [← h]; simp
                have h1 := (e.symm s).isLt
                have h3 : (e.symm s).val ≠ Fintype.card V - 1 := fun h => this (Fin.ext h)
                show (e.symm s).val ≤ Fintype.card V - 2
                omega
              · rw [hμ, hμ, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
                apply hH.eigenvalues₀_antitone
                show Fintype.card V - 2 ≤ Fintype.card V - 1
                omega
            have hN : 2 ≤ Fintype.card (∀ j, W j) := by
              rw [Fintype.card_pi]
              calc 2 ≤ Fintype.card (W ⟨0, hl⟩) := hcard _
                _ ≤ ∏ j, Fintype.card (W j) :=
                  Finset.single_le_prod' (f := fun j => Fintype.card (W j)) (fun j _ => Fintype.card_pos) (Finset.mem_univ _)
            choose Φ μ bot sec hsym heig horth hcomp hnn hbs hsec hge hbl using
              fun j => SPEC (W j) ((G j).lapMatrix ℝ) (SimpleGraph.posSemidef_lapMatrix ℝ (G j)) (hcard j)
            obtain ⟨ΦP, μP, botP, secP, hsymP, heigP, horthP, hcompP, hnnP, hbsP, hsecP, hgeP, hblP⟩ :=
              SPEC _ ((boxPi G).lapMatrix ℝ) (SimpleGraph.posSemidef_lapMatrix ℝ _) hN
            have hl1 : ∀ j, AlonMilman.Diameter.lambda1 (G j) = μ j (sec j) := by
              intro j; unfold AlonMilman.Diameter.lambda1; rw [dif_pos (hcard j), hsec j]
            have hlP : AlonMilman.Diameter.lambda1 (boxPi G) = μP secP := by
              unfold AlonMilman.Diameter.lambda1; rw [dif_pos hN, hsecP]
            have KER : ∀ j i, μ j i * ∑ w, Φ j i w = 0 := by
              intro j i
              have := SYM (W j) _ (hsym j) (Φ j i) (fun _ => 1)
              rw [heig j i, SimpleGraph.lapMatrix_mulVec_const_eq_zero] at this
              simp only [Pi.smul_apply, smul_eq_mul, mul_one, Pi.zero_apply, mul_zero,
                Finset.sum_const_zero] at this
              rw [Finset.mul_sum]; exact this
            have ONE : ∀ j y, ∑ i, (∑ w, Φ j i w) * Φ j i y = 1 := by
              intro j y
              simp only [Finset.sum_mul]; rw [Finset.sum_comm]; simp [hcomp j]
            have BOT0 : ∀ j, μ j (bot j) = 0 := by
              intro j
              obtain ⟨y⟩ := hne j
              have : ∃ i, ∑ w, Φ j i w ≠ 0 := by
                by_contra h; push_neg at h; have := ONE j y; simp [h] at this
              obtain ⟨i, hi⟩ := this
              have hμi : μ j i = 0 := by
                rcases mul_eq_zero.mp (KER j i) with h | h
                · exact h
                · exact absurd h hi
              have hle : μ j (bot j) ≤ μ j i := by
                by_cases hib : i = bot j
                · rw [hib]
                · exact le_trans (hbl j) (hge j i hib)
              exact le_antisymm (hle.trans hμi.le) (hnn j _)
            have CONST : ∀ j, 0 < μ j (sec j) → ∀ w, Φ j (bot j) w = 1 / ∑ w', Φ j (bot j) w' := by
              intro j hpos w
              have hz : ∀ i, i ≠ bot j → ∑ w, Φ j i w = 0 := by
                intro i hi
                have : 0 < μ j i := lt_of_lt_of_le hpos (hge j i hi)
                rcases mul_eq_zero.mp (KER j i) with h | h
                · linarith
                · exact h
              have h1 := ONE j w
              rw [Finset.sum_eq_single (bot j) (fun i _ hi => by rw [hz i hi, zero_mul]) (by simp)] at h1
              rw [eq_div_iff (left_ne_zero_of_mul_eq_one h1), mul_comm]; exact h1
            let T : (∀ j, W j) → (∀ j, W j) → ℝ := fun σ x => ∏ j, Φ j (σ j) (x j)
            let μT : (∀ j, W j) → ℝ := fun σ => ∑ j, μ j (σ j)
            have Tcomp : ∀ x y, ∑ σ, T σ x * T σ y = if x = y then 1 else 0 := by
              intro x y
              simp only [T, ← Finset.prod_mul_distrib]
              rw [← Fintype.prod_sum (fun j i => Φ j i (x j) * Φ j i (y j))]
              simp only [hcomp, Finset.prod_boole]
              by_cases h : x = y
              · subst h; simp
              · rw [if_neg h, if_neg]; intro h'; exact h (funext fun i => h' i (Finset.mem_univ i))
            have Torth : ∀ σ τ, ∑ x, T σ x * T τ x = if σ = τ then 1 else 0 := by
              intro σ τ
              simp only [T, ← Finset.prod_mul_distrib]
              rw [← Fintype.prod_sum (fun j w => Φ j (σ j) w * Φ j (τ j) w)]
              simp only [horth, Finset.prod_boole]
              by_cases h : σ = τ
              · subst h; simp
              · rw [if_neg h, if_neg]; intro h'; exact h (funext fun i => h' i (Finset.mem_univ i))
            have Teig : ∀ σ, Matrix.mulVec ((boxPi G).lapMatrix ℝ) (T σ) = μT σ • T σ := by
              intro σ; funext x
              rw [SimpleGraph.lapMatrix_mulVec_apply, NB, deg_eq]
              have hj : ∀ j, ((G j).degree (x j) : ℝ) * Φ j (σ j) (x j) -
                  ∑ w ∈ (G j).neighborFinset (x j), Φ j (σ j) w = μ j (σ j) * Φ j (σ j) (x j) := by
                intro j
                have := congrFun (heig j (σ j)) (x j)
                rw [SimpleGraph.lapMatrix_mulVec_apply] at this
                simpa using this
              have hu : ∀ j w, T σ (Function.update x j w) =
                  Φ j (σ j) w * ∏ k ∈ Finset.univ.erase j, Φ k (σ k) (x k) := by
                intro j w
                simp only [T]
                rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
                simp only [Function.update_self]
                congr 1
                refine Finset.prod_congr rfl fun k hk => ?_
                rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
              have hx : ∀ j, T σ x = Φ j (σ j) (x j) * ∏ k ∈ Finset.univ.erase j, Φ k (σ k) (x k) :=
                fun j => (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
              simp only [hu, ← Finset.sum_mul]
              push_cast
              rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
              simp only [Pi.smul_apply, smul_eq_mul, μT, Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hx j, ← Finset.sum_mul]
              linear_combination (∏ k ∈ Finset.univ.erase j, Φ k (σ k) (x k)) * hj j
            rw [hlP, show (fun j => AlonMilman.Diameter.lambda1 (G j)) = fun j => μ j (sec j) from funext hl1]
            apply le_antisymm
            · apply Finset.le_inf'
              intro j _
              let σ0 : ∀ k, W k := fun k => bot k
              let τ : ∀ k, W k := Function.update σ0 j (sec j)
              have hστ : σ0 ≠ τ := by
                intro h; have := congrFun h j; simp [τ, σ0] at this; exact hbs j this
              have hμ0 : μT σ0 = 0 := by simp [μT, σ0, BOT0]
              have hμτ : μT τ = μ j (sec j) := by
                simp only [μT]; rw [Finset.sum_eq_single j]
                · simp [τ]
                · intro k _ hk; simp [τ, Function.update_of_ne hk, σ0, BOT0]
                · simp
              obtain ⟨a, b, hab, hpos⟩ := PICK (∑ x, ΦP botP x * T σ0 x) (∑ x, ΦP botP x * T τ x)
              obtain ⟨h1, h2⟩ := TWO _ _ ((boxPi G).lapMatrix ℝ) T μT Teig Torth σ0 τ hστ a b
              obtain ⟨g1, g2⟩ := GEN _ _ ((boxPi G).lapMatrix ℝ) ΦP μP hsymP heigP hcompP
                (fun x => a * T σ0 x + b * T τ x)
              beta_reduce at g1 g2
              have hc0 : ∑ x, ΦP botP x * (a * T σ0 x + b * T τ x) = 0 := by
                rw [← hab]; simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
                congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_ <;> ring
              have hlow : μP secP * ∑ i, (∑ x, ΦP i x * (a * T σ0 x + b * T τ x)) ^ 2 ≤
                  ∑ i, μP i * (∑ x, ΦP i x * (a * T σ0 x + b * T τ x)) ^ 2 := by
                rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _ => ?_
                by_cases hi : i = botP
                · subst hi; rw [hc0]; simp
                · exact mul_le_mul_of_nonneg_right (hgeP i hi) (sq_nonneg _)
              rw [← g1, h1, ← g2, h2, hμ0, hμτ] at hlow
              have := hnn j (sec j)
              by_contra hc; push_neg at hc
              nlinarith [mul_lt_mul_of_pos_left hc hpos, sq_nonneg a, mul_nonneg (sq_nonneg a) this]
            · set m := Finset.univ.inf' ⟨⟨0, hl⟩, Finset.mem_univ _⟩ (fun j => μ j (sec j)) with hm
              have hmj : ∀ j, m ≤ μ j (sec j) := fun j => Finset.inf'_le _ (Finset.mem_univ j)
              obtain ⟨a, b, hab, hpos⟩ := PICK (∑ x, ΦP botP x) (∑ x, ΦP secP x)
              obtain ⟨h1, h2⟩ := TWO _ _ ((boxPi G).lapMatrix ℝ) ΦP μP heigP horthP botP secP hbsP a b
              obtain ⟨g1, g2⟩ := GEN _ _ ((boxPi G).lapMatrix ℝ) T μT hsymP Teig Tcomp
                (fun x => a * ΦP botP x + b * ΦP secP x)
              beta_reduce at g1 g2
              have hsum : ∑ x, (a * ΦP botP x + b * ΦP secP x) = 0 := by
                rw [← hab, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              have hterm : ∀ σ, m * (∑ x, T σ x * (a * ΦP botP x + b * ΦP secP x)) ^ 2 ≤
                  μT σ * (∑ x, T σ x * (a * ΦP botP x + b * ΦP secP x)) ^ 2 := by
                intro σ
                by_cases hσ : σ = fun k => bot k
                · by_cases hall : ∀ k, 0 < μ k (sec k)
                  · have : ∑ x, T σ x * (a * ΦP botP x + b * ΦP secP x) = 0 := by
                      have hT : ∀ x, T σ x = ∏ k, (1 / ∑ w', Φ k (bot k) w') := by
                        intro x; simp only [T, hσ]
                        exact Finset.prod_congr rfl fun k _ => CONST k (hall k) (x k)
                      simp only [hT, ← Finset.mul_sum, hsum, mul_zero]
                    rw [this]; simp
                  · push_neg at hall; obtain ⟨k, hk⟩ := hall
                    have hm0 : m ≤ 0 := (hmj k).trans hk
                    have : 0 ≤ μT σ := Finset.sum_nonneg fun k _ => hnn k _
                    nlinarith [sq_nonneg (∑ x, T σ x * (a * ΦP botP x + b * ΦP secP x))]
                · have : ∃ k, σ k ≠ bot k := by
                    by_contra h; push_neg at h; exact hσ (funext h)
                  obtain ⟨k, hk⟩ := this
                  have : μ k (σ k) ≤ μT σ :=
                    Finset.single_le_sum (f := fun k => μ k (σ k)) (fun k _ => hnn k _) (Finset.mem_univ k)
                  exact mul_le_mul_of_nonneg_right ((hmj k).trans ((hge k (σ k) hk).trans this))
                    (sq_nonneg _)
              have hS := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hterm σ
              rw [← Finset.mul_sum, ← g1, ← g2, h1, h2] at hS
              by_contra hc; push_neg at hc
              nlinarith [mul_lt_mul_of_pos_left hc hpos, mul_nonneg (sq_nonneg a) (sub_nonneg.2 hblP)]
