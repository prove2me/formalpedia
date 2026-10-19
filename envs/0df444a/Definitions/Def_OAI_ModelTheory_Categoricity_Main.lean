-- Prove2me | Definitions.Def_OAI_ModelTheory_Categoricity_Main
-- name    : OAI_ModelTheory_Categoricity_Main
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:55:20.602233+00:00
-- url     : https://prove2.me/theorems/786a228a-8e3e-45f3-bf51-c68eb1f8e547
-- title:
--   Countable-base arrays and the endpoint array on $V_{\omega_2}$ with base $\omega_1 \times_{\mathrm{lex}} \mathbb{Q}$
-- statement:
--   This file defines the concrete arrays that witness existence and non-categoricity in the counterexample under CH ($2^{\aleph_0} = \aleph_1$). Recall that an array $M$ consists of a nonempty index set $I_M$, a nonempty base $B_M$ that is a dense linear order without endpoints in which every closed interval is countable, and for every injective finite tuple $t = (x_0, \dots, x_k)$ from $I_M$ a binary matrix $\chi^M_t : \mathbb{N} \times B_M \to \{0,1\}$. Throughout, $\omega_1$ is the first uncountable ordinal, viewed as the well-ordered set of countable ordinals.
--
--   1. **Rational base.** The rationals $\mathbb{Q}$ with their usual order, a countable dense linear order without endpoints.
--
--   2. **Countable-base arrays.** For a cardinal $\mu \ge \aleph_0$, the array $Z_\mu$ has as index set the initial ordinal of $\mu$ (a set of cardinality $\mu$), base $\mathbb{Q}$, and all matrices zero:
--   $$
--   \chi^{Z_\mu}_t(n, q) = 0 \qquad \text{for every tuple } t,\ n \in \mathbb{N},\ q \in \mathbb{Q}.
--   $$
--   Its closed intervals are countable because $\mathbb{Q}$ is countable.
--
--   3. **The base $\omega_1 \times_{\mathrm{lex}} \mathbb{Q}$.** $B_{\mathrm{end}} = \omega_1 \times \mathbb{Q}$ ordered lexicographically, $(\beta, q) < (\beta', q')$ iff $\beta < \beta'$, or $\beta = \beta'$ and $q < q'$; it consists of $\aleph_1$ consecutive copies of $\mathbb{Q}$. The file records that $\omega_1$ is nonempty, that every initial segment $\{\beta' \in \omega_1 : \beta' \le \beta\}$ is countable, that consequently every closed interval of $B_{\mathrm{end}}$ is countable, and that $|B_{\mathrm{end}}| = \aleph_1$; it fixes a bijection $\pi : B_{\mathrm{end}} \to \omega_1$ (no order condition) and notes $\beth_{\omega_2} \ge \aleph_0$.
--
--   4. **The endpoint array.** Assume CH. Let $V_{\omega_2}$ be the von Neumann level at $\omega_2$, the set of all sets of rank below $\omega_2$; it has cardinality $\beth_{\omega_2}$. The endpoint array $E$ has index set $V_{\omega_2}$, base $B_{\mathrm{end}}$, and
--   $$
--   \chi^{E}_t(n, b) = r\big(c(t, \pi(b))\big)(n),
--   $$
--   where a colour is a binary sequence modulo finite modifications, $r$ picks a representative sequence of each colour, and $c(t,\beta)$ is the colour of $t$ at the tag $\beta \in \omega_1$. This colour is the image, under a fixed injective coding of finite diagrams into colours (available under CH), of the membership diagram of $t$ at $\beta$. The labels of this diagram are pairs $\ell = (J, m)$ with $J \subseteq \{0, \dots, k\}$ nonempty and $m \in \mathbb{N}$; the entry $y_\ell \in V_{\omega_2}$ is the $m$-th element of a fixed enumeration of a countable hull of $\{x_j : j \in J\}$, closed under chosen witnesses that separate distinct sets by membership. The diagram records which entries are equal and which are members of which, and tags each entry $y_\ell$ with the countable ordinal $f_{\operatorname{rank}(y_\ell)}(\beta)$. Here $(f_\alpha)_{\alpha < \omega_2}$ is the fixed sequence of functions $\omega_1 \to \omega_1$ given by $f_\alpha(\beta) = \sup\{ f_\gamma(\beta) + 1 : \gamma < \alpha,\ e_\alpha(\gamma) < \beta \}$ for chosen injections $e_\alpha : \alpha \to \omega_1$.
--
--   The arrays $Z_\mu$ give models of every infinite cardinality $\mu$, which provides the existence part of categoricity. The arrays $Z_{\beth_{\omega_2}}$ and $E$ give the two non-isomorphic models of size $\beth_{\omega_2}$: both index sets have cardinality $\beth_{\omega_2}$, but the bases have different cardinalities, $\aleph_0$ and $\aleph_1$. The colours of $E$ are arranged so that, for each tuple, the coded diagram is valid at all but countably many tags, which makes $E$ a member of the class.
--
--   **Formalization Note** `RationalBase` is `ULift ℚ`, with instances for density and the absence of endpoints. `countableData μ hμ` takes a proof `hμ : ℵ₀ ≤ μ` and uses `μ.ord.ToType` as index set. `Base` is `Tag ×ₗ RationalBase` with `Tag = (ω_ 1).ToType`; `tag_nonempty`, `tag_initial_countable`, `locallyCountable`, `base_cardinal`, `baseEquiv` (chosen by `Classical.choice`) and `endpoint_infinite` are the facts of item 3. `data hCH` uses `EndpointDiagrams.D`, a copy of `ZFSet.vonNeumann (ω_ 2)` in universe `u`, the colouring `EndpointDiagrams.colors hCH`, and `Colors.representative`, which is `Quotient.out`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/Main.lean

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/Main.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CHObstruction mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors
import Definitions.Def_OAI_ModelTheory_Categoricity_EndpointDiagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_TailBound
import Definitions.Def_OAI_ModelTheory_Categoricity_Arrays
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayMaps
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayEmbeddings
import Definitions.Def_OAI_ModelTheory_Categoricity_Subarrays
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayIsomorphisms
import Definitions.Def_OAI_ModelTheory_Categoricity_DirectedLimits
import Definitions.Def_OAI_ModelTheory_Categoricity_AEC

namespace OAI

/-!
# A CH obstruction to a prescribed categoricity threshold

Under CH, a countable relational language admits an abstract elementary class
with least Löwenheim–Skolem number `aleph0`, two nonisomorphic models of size
`beth (omega 2) = hanf aleph0`, and categoricity, including existence, at every
cardinal at least `tailThreshold`. Distinct base cardinalities separate the
endpoint models, while finite-support row and column translations establish
the included categoricity tail.
-/

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Arrays

open Tuples

variable (hCH : CH.{u})

namespace Existence

abbrev RationalBase := ULift.{u} ℚ

instance : DenselyOrdered RationalBase.{u} where
  dense a b h := by
    obtain ⟨c, hc, hd⟩ := exists_between (show a.down < b.down from h)
    exact ⟨⟨c⟩, hc, hd⟩

instance : NoMinOrder RationalBase.{u} where
  exists_lt a := by
    obtain ⟨b, hb⟩ := exists_lt a.down
    exact ⟨⟨b⟩, hb⟩

instance : NoMaxOrder RationalBase.{u} where
  exists_gt a := by
    obtain ⟨b, hb⟩ := exists_gt a.down
    exact ⟨⟨b⟩, hb⟩

def countableData (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) : Data.{u} where
  I := μ.ord.ToType
  B := RationalBase
  indexNonempty := by
    have : Infinite μ.ord.ToType := Cardinal.aleph0_le_mk_iff.1 (by simpa using hμ)
    infer_instance
  baseNonempty := inferInstance
  order := inferInstance
  dense := inferInstance
  noMin := inferInstance
  noMax := inferInstance
  locallyCountable _ _ := Set.to_countable _
  bits _ _ _ := false

end Existence

namespace Categoricity

end Categoricity

namespace EndpointModels

open Diagrams
open Existence

abbrev Base := Tag.{u} ×ₗ RationalBase.{u}

instance tag_nonempty : Nonempty Tag.{u} := Ordinal.nonempty_toType_iff.2 (Ordinal.omega_pos 1).ne'

theorem tag_initial_countable (b : Tag.{u}) : (Set.Iic b).Countable := by
  have : Countable (Set.Iio b) := by
    apply Cardinal.mk_le_aleph0_iff.1
    apply Cardinal.lt_aleph_one_iff.1
    simpa only [Cardinal.mk_toType, Ordinal.card_omega] using
      (Cardinal.mk_Iio_lt b (by simp [Tag]))
  have h : Set.Iic b = insert b (Set.Iio b) := by
    ext x
    simp only [Set.mem_Iic, Set.mem_insert_iff, Set.mem_Iio, le_iff_eq_or_lt]
  rw [h]
  exact (Set.to_countable (Set.Iio b)).insert b

theorem locallyCountable (a b : Base.{u}) : (Set.Icc a b).Countable := by
  have := (tag_initial_countable (ofLex b).1).to_subtype
  let f : Set.Icc a b → Set.Iic (ofLex b).1 × RationalBase.{u} :=
    fun x => (⟨(ofLex x.val).1, Prod.Lex.monotone_fst _ _ x.property.2⟩, (ofLex x.val).2)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply ofLex.injective
    exact Prod.ext (congrArg (fun z : Set.Iic (ofLex b).1 × RationalBase.{u} => z.1.val) h)
      (congrArg (fun z : Set.Iic (ofLex b).1 × RationalBase.{u} => z.2) h)
  exact Set.countable_coe_iff.1 hf.countable

theorem base_cardinal : #Base.{u} = (ℵ_ 1 : Cardinal.{u}) := by
  rw [Cardinal.mk_congr (ofLex : Base.{u} ≃ _), Cardinal.mk_prod]
  simp [Tag, RationalBase]

def baseEquiv : Base.{u} ≃ Tag.{u} := Classical.choice (Cardinal.eq.1 (by
  rw [base_cardinal, Cardinal.mk_toType, Ordinal.card_omega]))

theorem endpoint_infinite : ℵ₀ ≤ endpoint.{u} := Cardinal.aleph0_le_beth _

def data (hCH : CH.{u}) : Data.{u} where
  I := EndpointDiagrams.D
  B := Base
  indexNonempty := by
    have : Infinite EndpointDiagrams.D.{u} := Cardinal.aleph0_le_mk_iff.1
      (EndpointDiagrams.cardinal.symm ▸ endpoint_infinite)
    infer_instance
  baseNonempty := inferInstance
  order := inferInstance
  dense := inferInstance
  noMin := inferInstance
  noMax := inferInstance
  locallyCountable := locallyCountable
  bits t n b := Colors.representative (EndpointDiagrams.colors hCH t (baseEquiv b)).down n

end EndpointModels

end Arrays

end CHObstruction

end

end OAI


