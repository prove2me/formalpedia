-- Prove2me | Definitions.Def_LowAccLTC_colorRestrict
-- name    : LowAccLTC_colorRestrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:20.592389+00:00
-- url     : https://prove2.me/theorems/178755ae-853e-4fa3-90af-c3322b44eb12
-- title:
--   Even and good partitions, and the colour-restricted faces complex $Y^{\mathcal P}$
-- statement:
--   An **even partition** $\mathcal P:[r]\to[k]$ into blocks of size $j$ is a map all of whose fibres have $j$ elements. It is **good** if for all blocks $a\neq b$ the set $\mathcal P^{-1}(\{a,b\})$ contains no four cyclically consecutive colours: $\{i,i+1,i+2,i+3\}\not\subseteq\mathcal P^{-1}(\{a,b\})$ for every $i$, indices modulo $r$.
--
--   For a weighted $r$-partite complex $X$ and $\mathcal P$, the **$\mathcal P$-restricted faces complex** $Y^{\mathcal P}$ is the subcomplex of $\mathcal F^jX$ induced on the $j$-faces whose colour set is a block $\mathcal P^{-1}(a)$; such a vertex gets colour $a$, so $Y^{\mathcal P}$ is $k$-partite. Its top faces are the top faces of $X$ with the measure of $X$: the top face $t$ has as vertex of colour $a$ the face of $t$ with colours $\mathcal P^{-1}(a)$. The module also defines the union of the $j$-faces of a face of $Y^{\mathcal P}$.
--
--   These objects are used in the colour-restriction Lemma 5.4, in Claim 5.9 and in Claim 5.12.
--
--   **Formalization Note** A vertex of $Y^{\mathcal P}$ is the pair (colour, $j$-face of $X$).
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Definition 2.14 p.17 (PDF p.20), Definition 5.3 p.44 (PDF p.47), §5.2.1 p.47 (PDF p.50)

import Definitions.Def_LowAccLTC_PartiteComplex

namespace LowAccLTC

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs*,
unpublished manuscript (sha256 04242e17…); page references are printed pages (PDF page − 3). -/

/-- `P : [r] → [k]` is an even partition into blocks of size `j` (§2.3, Definition 2.14, p.17;
Definition 5.3, p.44): every fibre `P⁻¹(a)` has exactly `j` elements. -/
def IsEvenPartition {r k : ℕ} (j : ℕ) (P : Fin r → Fin k) : Prop :=
  ∀ a, (Finset.univ.filter (fun c => P c = a)).card = j

/-- The finite set of even partitions `P : [r] → [k]` with blocks of size `j`. -/
noncomputable def evenPartitions (r j k : ℕ) : Finset (Fin r → Fin k) := by
  classical exact Finset.univ.filter (fun P => IsEvenPartition j P)

/-- The colour `i + n` taken modulo `r`. -/
def cyc {r : ℕ} (i : Fin r) (n : ℕ) : Fin r :=
  ⟨(i.val + n) % r, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- A good even partition (§5.2.1, p.47): for all blocks `a ≠ b`, `P⁻¹({a, b})` contains no
four cyclically consecutive colours, i.e. `{i, i+1, i+2, i+3} ⊈ P⁻¹({a, b})` for every `i`, with
indices modulo `r`. -/
def IsGoodPartition {r k : ℕ} (P : Fin r → Fin k) : Prop :=
  ∀ a b : Fin k, a ≠ b → ∀ i : Fin r, ¬ ∀ n < 4, P (cyc i n) = a ∨ P (cyc i n) = b

namespace PartiteComplex

variable {r : ℕ} {V T : Type*} [Fintype T] (X : PartiteComplex r V T)

/-- The `P`-restricted faces complex `Y^P` (Definition 2.14, p.17; Definition 5.3, p.44): the
subcomplex of the `j`-faces complex `F^j X` induced on the `j`-faces whose colour set is a block
`P⁻¹(a)`; such a vertex gets the colour `a`. Its top faces are the top faces of `X`, with the
measure of `X`, and the vertex of colour `a` of the top face `t` is the face of `t` with colour
set `P⁻¹(a)`.

**Formalization Note.** A vertex of `Y^P` is encoded as the pair `(a, s)` of its colour and the
`j`-face `s` of `X`; the tag `a` is determined by `s` (it is the block containing `col(s)`). -/
noncomputable def colorRestrict {k : ℕ} (P : Fin r → Fin k) :
    PartiteComplex k (Fin k × Finset V) T where
  col := Prod.fst
  vert t a := (a, X.face t (Finset.univ.filter (fun c => P c = a)))
  col_vert _ _ := rfl
  vert_inj := by
    classical
    intro t t' h
    apply X.vert_inj
    funext c
    have h1 := congrArg (fun F => (F (P c)).2) h
    simp only at h1
    have hm : X.vert t c ∈ X.face t (Finset.univ.filter (fun c' => P c' = P c)) := by
      unfold face
      exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
    rw [h1] at hm
    unfold face at hm
    obtain ⟨c', _, hc'⟩ := Finset.mem_image.mp hm
    have hcol := congrArg X.col hc'
    rw [X.col_vert, X.col_vert] at hcol
    subst hcol
    exact hc'.symm
  μ := X.μ
  μ_pos := X.μ_pos
  μ_sum := X.μ_sum

/-- The face of `X` underlying a face of `Y^P` (the union of its `j`-faces). -/
noncomputable def unionFace {k : ℕ} (S : Finset (Fin k × Finset V)) : Finset V := by
  classical exact S.biUnion Prod.snd

end PartiteComplex

end LowAccLTC


