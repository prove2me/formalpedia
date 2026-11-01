-- Prove2me | Definitions.Def_MVBlossoms_IsSegmentFrom
-- name    : MVBlossoms_IsSegmentFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:07.05066+00:00
-- url     : https://prove2.me/theorems/b564bd77-2dd1-43c9-8b56-25c18d812924
-- title:
--   The subpath $p[b\text{ to }u]$ read from $b$
-- statement:
--   Let $p$ be a walk and let $b$ and $u$ lie on it. The **subpath $p[b\text{ to }u]$** is the part of $p$ between $b$ and $u$, traversed from $b$ towards $u$; $b$ may come before or after $u$ on $p$.
--
--   The predicate holds for $q$ (a walk from $b$ to $u$) when $p=p_1\,q\,p_2$ (if $b$ comes first) or $p=p_1\,q^{-1}\,p_2$ (if $u$ comes first), where $q^{-1}$ is $q$ reversed. On a simple path $q$ is unique.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 7, p.2016; Definitions 24 and 33, pp.2032, 2038

import Mathlib

namespace MVBlossoms

/-- **The subpath `p[b to u]`, read from b.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 7, p.2016 ("Other
combinations are self-explanatory") as used in Definitions 24 (p.2032) and 33 (p.2038): "Note that
we are allowing b to appear either before or after u on path p."

`IsSegmentFrom p q` for `p : G.Walk f v` and `q : G.Walk b u`: `q` is the part of `p` between `b`
and `u`, traversed from `b` to `u`. Either `b` comes first and `p = p₁ ++ q ++ p₂`, or `u` comes
first and `p = p₁ ++ reverse q ++ p₂`.

**Formalization Note.** When `p` is a simple path and `b, u` lie on it, exactly one such `q`
exists, so "p[b to u] is ..." is stated as "some `q` with `IsSegmentFrom p q` is ...". -/
def IsSegmentFrom {V : Type} {G : SimpleGraph V} {f v b u : V} (p : G.Walk f v)
    (q : G.Walk b u) : Prop :=
  (∃ (p₁ : G.Walk f b) (p₂ : G.Walk u v), p = p₁.append (q.append p₂)) ∨
    (∃ (p₁ : G.Walk f u) (p₂ : G.Walk b v), p = p₁.append (q.reverse.append p₂))

end MVBlossoms


