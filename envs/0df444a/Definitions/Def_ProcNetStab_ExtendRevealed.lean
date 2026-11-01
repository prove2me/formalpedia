-- Prove2me | Definitions.Def_ProcNetStab_ExtendRevealed
-- name    : ProcNetStab_ExtendRevealed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:32.488305+00:00
-- url     : https://prove2.me/theorems/e5215beb-3649-401d-a552-babfa008691b
-- title:
--   ExtendRevealed (Algorithm 1): closing a revealed profile under $k$-anonymity
-- statement:
--   Let $g$ be the observed network, $k \in \mathbb N$, $L$ a type map and $C$ a choice of revealing endpoints with revealed profile $\langle R, P\rangle$. Call $(a, h, b)$ and $(a', h', b')$ **similar** if $(a, h) \simeq_k (a', h')$ and $(a, h - ab) \simeq_k (a', h' - a'b')$. The extension $\langle R^*, P^*\rangle$ produced by ExtendRevealed is the least profile of relations such that
--
--   1. $R_a \subseteq R^*_a$ and $P_a \subseteq P^*_a$ for every agent $a$;
--   2. if $(h, h - ab) \in R^*_a$ and $(a, h, b)$ is similar to $(a', h', b')$, then $(h', h' - a'b') \in R^*_{a'}$;
--   3. if $(h - ab, h) \in P^*_a$ and $(a, h, b)$ is similar to $(a', h', b')$, then $(h' - a'b', h') \in P^*_{a'}$;
--   4. $P^*_a \subseteq R^*_a$ for every agent $a$.
--
--   The extension adds exactly the comparisons that $k$-anonymity forces on any preference profile containing the revealed one.
--
--   **Formalization Note** Algorithm 1's single `foreach` pass, in unspecified order, is read as the fixpoint it describes (the paper notes that each iteration adds at least one ordered pair): an inductive predicate, with `true` for $R^*$ and `false` for $P^*$. The algorithm's `else` branch is not encoded; it only suppresses rule 3 at an event where rule 2 already fired, and those two pairs already form a cycle of length two, so acyclicity of the output does not depend on it.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Algorithm 1, p.OA-3

import Mathlib
import Definitions.Def_ProcNetStab_KIso
import Definitions.Def_ProcNetStab_ValidChoice

namespace ProcNetStab

/-- **ExtendRevealed** (Chiong, Qi, *Stability of Procurement Networks* (authors' manuscript,
2025), Algorithm 1, p.OA-3): the extension `⟨R*, P*⟩` of the revealed preference profile of the
choice `C` according to `≃k`. `ExtendRevealed L g k C true a x y` means `x R*_a y` and
`ExtendRevealed L g k C false a x y` means `x P*_a y`. It is the least profile that
* contains the revealed profile `⟨R, P⟩` of `C` (`revR`, `revP`);
* adds `(h', h' − a'b')` to `R*_{a'}` whenever `(h, h − ab) ∈ R*_a`, `(a, h) ≃k (a', h')` and
  `(a, h − ab) ≃k (a', h' − a'b')` (lines 3–4);
* adds `(h' − a'b', h')` to `P*_{a'}` whenever `(h − ab, h) ∈ P*_a` and the same two
  `≃k`-relations hold (lines 6–7);
* keeps `P*_a ⊆ R*_a` (line 8).

**Formalization Note** The algorithm's single `foreach` pass, whose order is unspecified, is read
as the fixpoint it describes ("At each iteration, we add at least one ordered pair", p.OA-3): the
least profile closed under both propagation rules. The `else` of line 5 is dropped; it only
suppresses the second rule at an event whose first rule already fired, which together with the
drop pair forms a cycle of length two, so acyclicity of the output does not depend on it. -/
inductive ExtendRevealed {V T : Type*} (L : V → T) (g : SimpleGraph V) (k : ℕ)
    (C : V → V → Prop) : Bool → V → SimpleGraph V → SimpleGraph V → Prop
  | baseR {a : V} {x y : SimpleGraph V} : revR g C a x y → ExtendRevealed L g k C true a x y
  | baseP {a : V} {x y : SimpleGraph V} : revP g C a x y → ExtendRevealed L g k C false a x y
  | propR {a b a' b' : V} {h h' : SimpleGraph V} :
      ExtendRevealed L g k C true a h (delLink h a b) →
      KIso L g k a h a' h' → KIso L g k a (delLink h a b) a' (delLink h' a' b') →
      ExtendRevealed L g k C true a' h' (delLink h' a' b')
  | propP {a b a' b' : V} {h h' : SimpleGraph V} :
      ExtendRevealed L g k C false a (delLink h a b) h →
      KIso L g k a h a' h' → KIso L g k a (delLink h a b) a' (delLink h' a' b') →
      ExtendRevealed L g k C false a' (delLink h' a' b') h'
  | PtoR {a : V} {x y : SimpleGraph V} :
      ExtendRevealed L g k C false a x y → ExtendRevealed L g k C true a x y

end ProcNetStab


